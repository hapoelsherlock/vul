import os
import re
import json
import warnings
import shutil
import urllib.request
from pathlib import Path
from collections import deque
import subprocess
import random

# --- Silence Third-Party Deprecation Warnings ---
warnings.filterwarnings("ignore", category=DeprecationWarning)

import tree_sitter_c as tsc
import tree_sitter_cpp as tscpp
from tree_sitter import Language, Parser

# --- Tree-Sitter Initialization ---
C_LANG = Language(tsc.language())
CPP_LANG = Language(tscpp.language())

C_PARSER = Parser(C_LANG)
CPP_PARSER = Parser(CPP_LANG)

def get_parser_and_lang(file_path: str):
    ext = Path(file_path).suffix.lower()
    if ext in ['.cpp', '.cc', '.cxx', '.h', '.hpp']:
        return CPP_PARSER, CPP_LANG
    return C_PARSER, C_LANG

# --- Helper Utilities ---
def run_cmd(args, cwd=None, timeout=60):
    try:
        # Explicitly enforce UTF-8 and ignore weird characters to prevent Windows cp1252 crashes
        res = subprocess.run(args, capture_output=True, encoding="utf-8", errors="ignore", cwd=cwd, timeout=timeout, check=True)
        return res.stdout
    except (subprocess.TimeoutExpired, subprocess.CalledProcessError):
        return ""

def sanitize_text(text: str) -> str:
    """Removes accidental hints or metadata leaks from code contexts."""
    if not text: return ""
    text = re.sub(r'CVE-\d{4}-\d+', '[CVE_REDACTED]', text, flags=re.IGNORECASE)
    text = re.sub(r'(fix|vuln|vulnerability|patch|security|issue|bug|crash|overflow|cve)[_-]?\d*', '[REDACTED]', text, flags=re.IGNORECASE)
    return text

def check_repo_languages_via_api(owner: str, repo: str, github_token: str = None) -> dict:
    """
    Queries GitHub's API to verify if the repo actually contains C/C++ code.
    Returns a dict with language breakdown and confidence score.
    """
    url = f"https://api.github.com/repos/{owner}/{repo}/languages"
    headers = {"User-Agent": "Mozilla/5.0 (VulnerabilityBenchmarkBuilder/1.0)"}
    
    if github_token:
        headers["Authorization"] = f"token {github_token}"
    
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=5) as response:
            languages = json.loads(response.read().decode())
            
            total_bytes = sum(languages.values())
            if total_bytes == 0:
                return {"has_c_cpp": False, "confidence": 0.0, "languages": languages}
            
            c_bytes = languages.get("C", 0)
            cpp_bytes = languages.get("C++", 0)
            c_cpp_ratio = (c_bytes + cpp_bytes) / total_bytes
            
            # High confidence if >50% of code is C/C++
            has_c_cpp = c_cpp_ratio >= 0.5
            confidence = c_cpp_ratio
            
            return {
                "has_c_cpp": has_c_cpp,
                "confidence": confidence,
                "c_bytes": c_bytes,
                "cpp_bytes": cpp_bytes,
                "total_bytes": total_bytes,
                "languages": languages
            }
    except Exception as e:
        # If API fails or rate-limits, return uncertainty
        return {"has_c_cpp": None, "confidence": 0.0, "error": str(e), "languages": {}}

def search_repos_for_c_cpp(github_token: str = None, stars_min: int = 100, language: str = "c") -> list:
    """
    Search for C/C++ repositories on GitHub that are likely to have real vulnerabilities.
    Returns top matching repos with language breakdown.
    """
    url = f"https://api.github.com/search/repositories?q=language:{language}+stars:>{stars_min}&sort=stars&order=desc&per_page=30"
    headers = {"User-Agent": "Mozilla/5.0 (VulnerabilityBenchmarkBuilder/1.0)", "Accept": "application/vnd.github.v3+json"}
    
    if github_token:
        headers["Authorization"] = f"token {github_token}"
    
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=10) as response:
            data = json.loads(response.read().decode())
            repos = []
            for item in data.get("items", []):
                repos.append({
                    "owner": item["owner"]["login"],
                    "name": item["name"],
                    "url": item["html_url"],
                    "stars": item["stargazers_count"],
                    "forks": item["forks_count"],
                    "description": item["description"],
                    "language": item["language"]
                })
            return repos
    except Exception as e:
        print(f"[!] Error searching repos: {e}")
        return []

# --- Core Tree-Sitter Indexing ---
def query_ast(node, query_str, lang):
    query = lang.query(query_str)
    captures = query.captures(node)
    return captures

def extract_functions_and_macros(file_path: str, source_code: str):
    parser, lang = get_parser_and_lang(file_path)
    tree = parser.parse(bytes(source_code, "utf8"))
    root = tree.root_node

    functions = {}
    macros = {}

    macro_q = "(preproc_def name: (identifier) @name value: (_) @val)" if lang == C_LANG else "(preproc_def name: (identifier) @name)"
    for node, tag in query_ast(root, macro_q, lang):
        if tag == "name":
            macros[node.text.decode('utf8', errors='ignore')] = source_code[node.start_byte:node.end_byte]

    func_q = "(function_definition) @func"
    func_nodes = [cap[0] for cap in query_ast(root, func_q, lang)]

    for fn in func_nodes:
        name_node = None
        decl_q = "(function_definition declarator: (_) @decl)"
        decls = query_ast(fn, decl_q, lang)
        if decls:
            id_q = "(identifier) @id"
            ids = query_ast(decls[0][0], id_q, lang)
            if ids:
                name_node = ids[-1][0]

        if not name_node:
            continue

        func_name = name_node.text.decode('utf8', errors='ignore')
        fn_text = source_code[fn.start_byte:fn.end_byte]
        
        call_q = "(call_expression function: (identifier) @callee)"
        callees = set()
        for c_node, _ in query_ast(fn, call_q, lang):
            callees.add(c_node.text.decode('utf8', errors='ignore'))

        functions[func_name] = {
            "name": func_name,
            "body": fn_text,
            "start_line": fn.start_point[0],
            "end_line": fn.end_point[0],
            "callees": list(callees)
        }

    return functions, macros

def find_vulnerable_function(file_path: str, source_code: str, target_line: int):
    funcs, _ = extract_functions_and_macros(file_path, source_code)
    for name, info in funcs.items():
        if info["start_line"] <= target_line <= info["end_line"]:
            return info
    return None

# --- Graph Traversal Context Collector ---
class RepoContextGraph:
    def __init__(self, repo_dir: Path):
        self.repo_dir = repo_dir
        self.file_indices = {}
        self.call_map = {}     
        self._build_index()

    def _build_index(self):
        extensions = {'.c', '.h', '.cpp', '.hpp', '.cc', '.cxx'}
        for root, _, files in os.walk(self.repo_dir):
            for file in files:
                if Path(file).suffix.lower() in extensions:
                    full_path = Path(root) / file
                    rel_path = str(full_path.relative_to(self.repo_dir))
                    try:
                        content = full_path.read_text(errors='ignore')
                        funcs, macros = extract_functions_and_macros(rel_path, content)
                        self.file_indices[rel_path] = (funcs, macros)
                        
                        for f_name, f_info in funcs.items():
                            for callee in f_info["callees"]:
                                if callee not in self.call_map:
                                    self.call_map[callee] = []
                                self.call_map[callee].append((rel_path, f_name))
                    except Exception:
                        continue

    def get_macros_used(self, body_text: str) -> list:
        tokens = set(re.findall(r'\b[A-Z_][A-Z0-9_]*\b', body_text))
        found = []
        for _, (_, macros) in self.file_indices.items():
            for m_name, m_code in macros.items():
                if m_name in tokens:
                    found.append({"macro": m_name, "code": sanitize_text(m_code)})
        return found[:10]

    def get_siblings(self, file_path: str, target_func: str, count=2) -> list:
        if file_path not in self.file_indices: return []
        funcs, _ = self.file_indices[file_path]
        siblings = [f["body"] for name, f in funcs.items() if name != target_func]
        random.shuffle(siblings)
        return [sanitize_text(s) for s in siblings[:count]]

    def resolve_callees(self, callee_names: list) -> list:
        resolved = []
        for name in callee_names:
            for file_path, (funcs, _) in self.file_indices.items():
                if name in funcs:
                    resolved.append({
                        "file_path": file_path,
                        "function": name,
                        "source": sanitize_text(funcs[name]["body"])
                    })
                    break
        return resolved[:5]

    def trace_callers_bfs(self, start_func: str, max_depth=3) -> list:
        visited = set()
        queue = deque([(start_func, 1)])
        results = []

        while queue:
            curr_func, depth = queue.popleft()
            if depth > max_depth or curr_func in visited:
                continue
            visited.add(curr_func)

            callers = self.call_map.get(curr_func, [])
            for file_path, caller_name in callers:
                if (file_path, caller_name) not in results:
                    funcs, _ = self.file_indices.get(file_path, ({}, {}))
                    if caller_name in funcs:
                        results.append({
                            "file_path": file_path,
                            "function": caller_name,
                            "depth": depth,
                            "source": sanitize_text(funcs[caller_name]["body"])
                        })
                        queue.append((caller_name, depth + 1))
        return results

    def extract_negative_samples(self, exclude_func: str = None, count: int = 5) -> list:
        """Extract random functions from repo that aren't the vulnerable one (negative samples)."""
        all_funcs = []
        for file_path, (funcs, _) in self.file_indices.items():
            for func_name, func_info in funcs.items():
                if exclude_func and func_name == exclude_func:
                    continue
                all_funcs.append({
                    "file": file_path,
                    "name": func_name,
                    "body": sanitize_text(func_info["body"]),
                    "lines": func_info["end_line"] - func_info["start_line"]
                })
        
        # Shuffle and prefer similarly-sized functions for harder discrimination
        random.shuffle(all_funcs)
        return all_funcs[:count]

    def get_external_lib_calls(self, func_body: str) -> list:
        """Extract library calls (stdlib, POSIX, etc.) to add realistic context."""
        common_libs = {
            'malloc', 'free', 'calloc', 'realloc',
            'strcpy', 'strcat', 'sprintf', 'printf', 'gets',
            'memcpy', 'memmove', 'memset',
            'open', 'read', 'write', 'close',
            'pthread_create', 'pthread_join',
            'socket', 'bind', 'listen', 'accept',
        }
        found = set()
        for lib_call in common_libs:
            if re.search(rf'\b{lib_call}\s*\(', func_body, re.IGNORECASE):
                found.add(lib_call)
        return list(found)

# --- Vulnerability Analysis & Classification ---
def infer_vuln_type(diff_out: str, vuln_func: str) -> str:
    """Heuristic classification of vulnerability type."""
    func_lower = vuln_func.lower()
    diff_lower = diff_out.lower()
    
    patterns = {
        "buffer_overflow": [r'strcpy', r'strcat', r'sprintf', r'gets', r'\[.*\].*=', r'memcpy.*size'],
        "use_after_free": [r'free\s*\(', r'delete\s+', r'realloc', r'->.*after.*free'],
        "integer_overflow": [r'\+\s*\w+', r'\*\s*\w+', r'<<', r'size.*\+'],
        "sql_injection": [r'query', r'sql', r'select.*from'],
        "format_string": [r'printf.*%', r'sprintf.*%', r'fprintf.*%'],
        "race_condition": [r'pthread', r'mutex', r'lock', r'thread'],
        "null_pointer_dereference": [r'->', r'\*\w+', r'\[\d+\]'],
    }
    
    scores = {}
    for vuln_type, pattern_list in patterns.items():
        score = 0
        for pattern in pattern_list:
            score += len(re.findall(pattern, diff_lower))
            score += len(re.findall(pattern, func_lower))
        if score > 0:
            scores[vuln_type] = score
    
    if scores:
        return max(scores, key=scores.get)
    return "unknown"

def analyze_patch_complexity(diff_out: str, target_file: str) -> dict:
    """Score patch difficulty based on scope and magnitude."""
    lines_added = len([l for l in diff_out.splitlines() if l.startswith('+')])
    lines_removed = len([l for l in diff_out.splitlines() if l.startswith('-')])
    lines_changed = lines_added + lines_removed
    
    files_touched = len(re.findall(r'^--- a/', diff_out, re.MULTILINE))
    hunks = len(re.findall(r'^@@', diff_out, re.MULTILINE))
    
    is_minimal = lines_changed <= 5
    is_scattered = files_touched > 1 or hunks > 3
    is_large = lines_changed > 50
    
    # Classify difficulty
    if is_minimal and not is_scattered:
        difficulty = "trivial"
    elif lines_changed < 20 and hunks <= 2:
        difficulty = "easy"
    elif lines_changed < 50 and not is_scattered:
        difficulty = "moderate"
    elif is_large or is_scattered:
        difficulty = "hard"
    else:
        difficulty = "moderate"
    
    return {
        "lines_added": lines_added,
        "lines_removed": lines_removed,
        "total_lines_changed": lines_changed,
        "files_touched": files_touched,
        "hunks": hunks,
        "is_minimal_patch": is_minimal,
        "is_scattered_fix": is_scattered,
        "is_large_patch": is_large,
        "difficulty_score": difficulty
    }

def extract_commit_message(repo_cache_dir: Path, sha: str) -> str:
    """Extract commit message (may or may not mention the vuln)."""
    msg = run_cmd(["git", "log", "-1", "--pretty=%B", sha], cwd=repo_cache_dir)
    return sanitize_text(msg) if msg else ""

def get_intermediate_commits(repo_cache_dir: Path, vuln_sha: str, target_file: str, max_commits: int = 3) -> list:
    """Fetch commits between vuln introduction and fix to add temporal confusion."""
    try:
        # Get commits after the vulnerable one
        log_output = run_cmd(["git", "log", "--oneline", f"{vuln_sha}..HEAD", "--", target_file], cwd=repo_cache_dir)
        if not log_output:
            return []
        
        commits = [line.split()[0] for line in log_output.splitlines()[:max_commits]]
        results = []
        
        for commit in commits:
            try:
                code = run_cmd(["git", "show", f"{commit}:{target_file}"], cwd=repo_cache_dir)
                if code:
                    msg = run_cmd(["git", "log", "-1", "--pretty=%s", commit], cwd=repo_cache_dir)
                    results.append({
                        "sha": commit,
                        "message": sanitize_text(msg),
                        "code_snippet": sanitize_text(code[:500])  # First 500 chars for context
                    })
            except Exception:
                continue
        
        return results
    except Exception:
        return []

def detect_conditional_compilation(func_body: str) -> list:
    """Detect #ifdef, #if defined, etc. that might affect compilation."""
    patterns = [
        r'#ifdef\s+(\w+)',
        r'#if\s+defined\s*\(\s*(\w+)\s*\)',
        r'#ifndef\s+(\w+)',
    ]
    conditions = []
    for pattern in patterns:
        matches = re.findall(pattern, func_body)
        conditions.extend(matches)
    return list(set(conditions))

def categorize_distractors(graph: RepoContextGraph, vuln_func_info: dict, target_file: str, count_per_level: int = 2) -> dict:
    """Create distractors at different difficulty levels."""
    negative_samples = graph.extract_negative_samples(exclude_func=vuln_func_info["name"], count=count_per_level * 3)
    
    vuln_size = vuln_func_info["end_line"] - vuln_func_info["start_line"]
    vuln_libs = set(graph.get_external_lib_calls(vuln_func_info["body"]))
    
    easy = []
    medium = []
    hard = []
    
    for sample in negative_samples:
        sample_libs = set(graph.get_external_lib_calls(sample["body"]))
        lib_overlap = len(vuln_libs & sample_libs) / max(len(vuln_libs), 1)
        size_similarity = abs(sample["lines"] - vuln_size) / max(vuln_size, 1)
        
        # Easy: completely different size and libraries
        if size_similarity > 2 or lib_overlap < 0.2:
            easy.append(sample)
        # Hard: similar size and libraries but different logic
        elif size_similarity < 0.5 and lib_overlap > 0.5:
            hard.append(sample)
        # Medium: somewhere in between
        else:
            medium.append(sample)
    
    return {
        "easy_distractors": easy[:count_per_level],
        "medium_distractors": medium[:count_per_level],
        "hard_distractors": hard[:count_per_level]
    }

# --- Processing Pipeline Engine ---
def process_single_cve(cve_json_path: Path, work_dir: Path, active_session_repos: set, github_token: str = None):
    with open(cve_json_path, 'r') as f:
        data = json.load(f)

    cve_id = data.get("cveMetadata", {}).get("cveId", "UNKNOWN")
    
    json_str = json.dumps(data)
    commit_matches = re.findall(r'github\.com/([\w-]+)/([\w-]+)/commit/([a-f0-9]{40})', json_str)
    if not commit_matches:
        return None

    owner, repo, sha = commit_matches[0]
    
    # --- GitHub API Optimization Filter ---
    lang_check = check_repo_languages_via_api(owner, repo, github_token)
    if not lang_check.get("has_c_cpp"):
        return None

    repo_url = f"https://github.com/{owner}/{repo}.git"
    repo_cache_dir = work_dir / f"{owner}_{repo}"

    print(f"\n[*] Match found in {cve_id}! Target repo: {owner}/{repo} (C/C++: {lang_check['confidence']:.1%})")
    active_session_repos.add(repo_cache_dir)

    if not repo_cache_dir.exists():
        print(f"    -> Repository not cached. Cloning shallow tree from GitHub...")
        run_cmd(["git", "clone", "--depth", "50", repo_url, str(repo_cache_dir)])
    
    run_cmd(["git", "fetch", "origin", sha], cwd=repo_cache_dir)
    
    parent_sha = run_cmd(["git", "cat-file", "-p", sha], cwd=repo_cache_dir)
    parent_match = re.search(r'parent\s([a-f0-9]{40})', parent_sha)
    if not parent_match:
        print(f"    -> Skipped: Could not trace parent commit for {sha}.")
        return None
        
    p_sha = parent_match.group(1)
    run_cmd(["git", "fetch", "origin", p_sha], cwd=repo_cache_dir)

    diff_out = run_cmd(["git", "diff", p_sha, sha], cwd=repo_cache_dir)
    
    target_file = None
    target_line = None
    file_header_re = re.compile(r'^--- a/(.*\.(?:c|cpp|cc|cxx|h|hpp))$')
    hunk_re = re.compile(r'^@@ -\d+,(\d+) \+\d+,\d+ @@')

    for line in diff_out.splitlines():
        fm = file_header_re.match(line)
        if fm:
            target_file = fm.group(1)
            continue
        hm = hunk_re.match(line)
        if hm and target_file:
            target_line = int(hm.group(1))
            break

    if not target_file or not target_line:
        print(f"    -> Skipped: Patch did not modify a C/C++ source code file.")
        return None

    run_cmd(["git", "checkout", "-f", p_sha], cwd=repo_cache_dir)
    
    full_file_path = repo_cache_dir / target_file
    if not full_file_path.exists():
        return None
        
    pre_patch_code = full_file_path.read_text(errors='ignore')

    vuln_func_info = find_vulnerable_function(target_file, pre_patch_code, target_line)
    if not vuln_func_info:
        print(f"    -> Skipped: Diff hunk line {target_line} dropped outside a traceable function declaration block.")
        return None

    print(f"    -> Building Graph Context around function: '{vuln_func_info['name']}'")
    graph = RepoContextGraph(repo_cache_dir)
    
    # --- Enhanced Context Collection ---
    patch_complexity = analyze_patch_complexity(diff_out, target_file)
    vuln_type = infer_vuln_type(diff_out, vuln_func_info["body"])
    commit_msg = extract_commit_message(repo_cache_dir, sha)
    intermediate_commits = get_intermediate_commits(repo_cache_dir, p_sha, target_file, max_commits=3)
    conditionals = detect_conditional_compilation(vuln_func_info["body"])
    distractors = categorize_distractors(graph, vuln_func_info, target_file, count_per_level=2)
    external_libs = graph.get_external_lib_calls(vuln_func_info["body"])
    
    enriched_context = {
        "vulnerable_file": target_file,
        "vulnerable_function_name": vuln_func_info["name"],
        "vulnerability_type": vuln_type,
        "callers_chain": graph.trace_callers_bfs(vuln_func_info["name"], max_depth=3),
        "callees": graph.resolve_callees(vuln_func_info["callees"]),
        "referenced_macros": graph.get_macros_used(vuln_func_info["body"]),
        "external_library_calls": external_libs,
        "conditional_compilation": conditionals,
        "sibling_distractors": graph.get_siblings(target_file, vuln_func_info["name"], count=2),
        "distractor_functions": distractors,
        "negative_samples": graph.extract_negative_samples(exclude_func=vuln_func_info["name"], count=3),
        "intermediate_patches": intermediate_commits,
        "patch_analysis": patch_complexity,
        "commit_message": commit_msg,
    }

    return {
        "cve_id": cve_id,
        "repo": f"{owner}/{repo}",
        "parent_sha": p_sha,
        "vulnerable_commit": sha,
        "vulnerable_code": sanitize_text(vuln_func_info["body"]),
        "context": enriched_context,
        "metadata": {
            "difficulty": patch_complexity["difficulty_score"],
            "vulnerability_type": vuln_type,
            "includes_false_positives": len(distractors["hard_distractors"]) > 0,
            "has_temporal_gap": len(intermediate_commits) > 0,
            "requires_conditional_reasoning": len(conditionals) > 0,
            "language_confidence": lang_check['confidence'],
        },
        "label": 1
    }

# --- Execution Entrypoint Orchestration ---
def main():
    # Get GitHub token from environment for better API rate limits
    github_token = os.getenv("GITHUB_TOKEN")
    if not github_token:
        print("[!] Warning: GITHUB_TOKEN not set. API rate limits will be lower. Set it with: export GITHUB_TOKEN=your_token")
    
    base_dir = Path("./vuln_benchmark_builder")
    base_dir.mkdir(exist_ok=True)
    
    cve_repo_dir = base_dir / "cvelistv5"
    output_file = base_dir / "hard_vuln_benchmark.json"
    
    if not cve_repo_dir.exists():
        print("[*] Performing sparse clone on cvelistv5...")
        run_cmd(["git", "clone", "--depth", "1", "--filter=blob:none", "--sparse", "https://github.com/CVEProject/cvelistv5.git", str(cve_repo_dir)])
        run_cmd(["git", "sparse-checkout", "set", "cves/2026"], cwd=cve_repo_dir)

    cve_paths = list((cve_repo_dir / "cves" / "2026").glob("**/*.json"))
    print(f"[*] Found {len(cve_paths)} CVE JSON files to scan.")
    
    # Break the sequential batch assignment patterns of CVE-IDs
    random.shuffle(cve_paths)

    dataset = []
    limit = 30  
    
    active_session_repos = set()
    cleanup_counter = 0

    for idx, path in enumerate(cve_paths):
        if len(dataset) >= limit:
            break
            
        print(f"[*] Scanning records index: {idx}/{len(cve_paths)} (Benchmark Progress: {len(dataset)}/{limit})", end="\r")
        
        try:
            record = process_single_cve(path, base_dir, active_session_repos, github_token)
            if record:
                dataset.append(record)
                print(f"[+] Successfully saved benchmark record {len(dataset)}/{limit} ({record['cve_id']})")
                cleanup_counter = 0  
            else:
                cleanup_counter += 1

            # Garbage Collection Check: If 10 consecutive entries fail, clean unutilized directories
            if cleanup_counter >= 10:
                if active_session_repos:
                    print(f"\n[!] Garbage Collection: Wiping {len(active_session_repos)} unutilized target repos to free disk space...")
                    for repo_path in list(active_session_repos):
                        if repo_path.exists():
                            try:
                                shutil.rmtree(repo_path, ignore_errors=True)
                            except Exception:
                                pass
                    active_session_repos.clear()
                cleanup_counter = 0 

        except Exception as e:
            cleanup_counter += 1
            continue

    with open(output_file, 'w') as out:
        json.dump(dataset, out, indent=2)
    print(f"\n[!] Done! Hard benchmark saved to {output_file.resolve()}")

if __name__ == "__main__":
    main()
