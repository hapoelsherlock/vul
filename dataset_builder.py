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
import sys

# --- Silence Third-Party Deprecation Warnings ---
warnings.filterwarnings("ignore", category=DeprecationWarning)

# --- Tree-Sitter Initialization (Fixed) ---
try:
    from tree_sitter import Language, Parser
    import tree_sitter_c as tsc
    import tree_sitter_cpp as tscpp
    
    C_LANG = Language(tsc.language())
    CPP_LANG = Language(tscpp.language())
    C_PARSER = Parser(C_LANG)
    CPP_PARSER = Parser(CPP_LANG)
except ImportError as e:
    print(f"[!] Tree-Sitter dependency error: {e}")
    print("[!] Install with: pip install tree-sitter tree-sitter-c tree-sitter-cpp")
    sys.exit(1)

def get_parser_and_lang(file_path: str):
    ext = Path(file_path).suffix.lower()
    if ext in ['.cpp', '.cc', '.cxx', '.h', '.hpp']:
        return CPP_PARSER, CPP_LANG
    return C_PARSER, C_LANG

# --- Disk Management ---
def get_disk_usage(path: Path) -> dict:
    """Get disk usage statistics for a path."""
    try:
        stat = shutil.disk_usage(path)
        return {
            "total_gb": stat.total / (1024**3),
            "used_gb": stat.used / (1024**3),
            "free_gb": stat.free / (1024**3),
            "percent_used": (stat.used / stat.total) * 100
        }
    except Exception:
        return {"total_gb": 0, "used_gb": 0, "free_gb": 0, "percent_used": 0}

def check_disk_space(work_dir: Path, required_gb: float = 2.0) -> bool:
    """Check if there's enough disk space."""
    disk_info = get_disk_usage(work_dir)
    available = disk_info["free_gb"]
    return available > required_gb

# --- Helper Utilities ---
def run_cmd(args, cwd=None, timeout=120):
    try:
        res = subprocess.run(
            args, 
            capture_output=True, 
            encoding="utf-8", 
            errors="ignore", 
            cwd=cwd, 
            timeout=timeout, 
            check=False
        )
        return res.stdout if res.returncode == 0 else ""
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return ""

def sanitize_text(text: str) -> str:
    """Removes accidental hints or metadata leaks from code contexts."""
    if not text: return ""
    text = re.sub(r'CVE-\d{4}-\d+', '[CVE_REDACTED]', text, flags=re.IGNORECASE)
    text = re.sub(r'(fix|vuln|vulnerability|patch|security|issue|bug|crash|overflow|cve)[_-]?\d*', '[REDACTED]', text, flags=re.IGNORECASE)
    return text

def check_repo_languages_via_api(owner: str, repo: str, github_token: str = None) -> dict:
    """Queries GitHub's API to verify if the repo actually contains C/C++ code."""
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
        return {"has_c_cpp": None, "confidence": 0.0, "error": str(e), "languages": {}}

# --- Core Tree-Sitter Indexing ---
def query_ast(node, query_str, lang):
    try:
        query = lang.query(query_str)
        captures = query.captures(node)
        return captures
    except Exception:
        return []

def extract_functions_and_macros(file_path: str, source_code: str):
    """Extract functions and macros from source code using Tree-Sitter."""
    try:
        parser, lang = get_parser_and_lang(file_path)
        tree = parser.parse(bytes(source_code, "utf8"))
        root = tree.root_node

        functions = {}
        macros = {}

        macro_q = "(preproc_def name: (identifier) @name)"
        for node, tag in query_ast(root, macro_q, lang):
            if tag == "name":
                try:
                    macros[node.text.decode('utf8', errors='ignore')] = source_code[node.start_byte:node.end_byte]
                except Exception:
                    continue

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
                try:
                    callees.add(c_node.text.decode('utf8', errors='ignore'))
                except Exception:
                    continue

            functions[func_name] = {
                "name": func_name,
                "body": fn_text,
                "start_line": fn.start_point[0],
                "end_line": fn.end_point[0],
                "callees": list(callees)
            }

        return functions, macros
    except Exception:
        return {}, {}

def find_vulnerable_function(file_path: str, source_code: str, target_line: int):
    """Find the function containing the target line."""
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
        """Index all C/C++ files in the repository."""
        extensions = {'.c', '.h', '.cpp', '.hpp', '.cc', '.cxx'}
        for root, _, files in os.walk(self.repo_dir):
            for file in files:
                if Path(file).suffix.lower() in extensions:
                    full_path = Path(root) / file
                    rel_path = str(full_path.relative_to(self.repo_dir))
                    try:
                        content = full_path.read_text(errors='ignore')
                        if not content or len(content) > 5_000_000:
                            continue
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
        if file_path not in self.file_indices: 
            return []
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
        
        random.shuffle(all_funcs)
        return all_funcs[:count]

    def get_external_lib_calls(self, func_body: str) -> list:
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
    func_lower = vuln_func.lower()
    diff_lower = diff_out.lower()
    
    patterns = {
        "buffer_overflow": [r'strcpy', r'strcat', r'sprintf', r'gets'],
        "use_after_free": [r'free\s*\(', r'delete\s+'],
        "integer_overflow": [r'size.*\+', r'size.*\*'],
        "format_string": [r'printf.*%', r'sprintf.*%'],
        "race_condition": [r'pthread', r'thread'],
        "null_pointer_dereference": [r'->', r'\*\w+'],
    }
    
    scores = {}
    for vuln_type, pattern_list in patterns.items():
        score = 0
        for pattern in pattern_list:
            score += len(re.findall(pattern, diff_lower))
            score += len(re.findall(pattern, func_lower))
        if score > 0:
            scores[vuln_type] = score
    
    return max(scores, key=scores.get) if scores else "unknown"

def analyze_patch_complexity(diff_out: str) -> dict:
    lines_added = len([l for l in diff_out.splitlines() if l.startswith('+')])
    lines_removed = len([l for l in diff_out.splitlines() if l.startswith('-')])
    lines_changed = lines_added + lines_removed
    
    files_touched = len(re.findall(r'^--- a/', diff_out, re.MULTILINE))
    hunks = len(re.findall(r'^@@', diff_out, re.MULTILINE))
    
    if lines_changed <= 5:
        difficulty = "trivial"
    elif lines_changed < 20:
        difficulty = "easy"
    elif lines_changed < 50:
        difficulty = "moderate"
    else:
        difficulty = "hard"
    
    return {
        "lines_added": lines_added,
        "lines_removed": lines_removed,
        "total_lines_changed": lines_changed,
        "files_touched": files_touched,
        "hunks": hunks,
        "difficulty_score": difficulty
    }

def extract_commit_message(repo_cache_dir: Path, sha: str) -> str:
    msg = run_cmd(["git", "log", "-1", "--pretty=%B", sha], cwd=repo_cache_dir)
    return sanitize_text(msg) if msg else ""

def get_intermediate_commits(repo_cache_dir: Path, vuln_sha: str, target_file: str, max_commits: int = 3) -> list:
    try:
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
                        "code_snippet": sanitize_text(code[:500])
                    })
            except Exception:
                continue
        
        return results
    except Exception:
        return []

def detect_conditional_compilation(func_body: str) -> list:
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

def categorize_distractors(graph: RepoContextGraph, vuln_func_info: dict, count_per_level: int = 2) -> dict:
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
        
        if size_similarity > 2 or lib_overlap < 0.2:
            easy.append(sample)
        elif size_similarity < 0.5 and lib_overlap > 0.5:
            hard.append(sample)
        else:
            medium.append(sample)
    
    return {
        "easy_distractors": easy[:count_per_level],
        "medium_distractors": medium[:count_per_level],
        "hard_distractors": hard[:count_per_level]
    }

# --- Processing Pipeline Engine ---
def process_single_cve(cve_json_path: Path, work_dir: Path, github_token: str = None):
    """Process a single CVE record and extract vulnerability context."""
    try:
        with open(cve_json_path, 'r') as f:
            data = json.load(f)
    except Exception:
        return None

    cve_id = data.get("cveMetadata", {}).get("cveId", "UNKNOWN")
    
    json_str = json.dumps(data)
    commit_matches = re.findall(r'github\.com/([\w-]+)/([\w-]+)/commit/([a-f0-9]{40})', json_str)
    if not commit_matches:
        return None

    owner, repo, sha = commit_matches[0]
    repo_key = f"{owner}/{repo}"
    
    # --- GitHub API Language Check ---
    lang_check = check_repo_languages_via_api(owner, repo, github_token)
    if not lang_check.get("has_c_cpp"):
        return None

    repo_url = f"https://github.com/{owner}/{repo}.git"
    repo_cache_dir = work_dir / f"{owner}_{repo}"

    print(f"\n[*] {cve_id}: {repo_key}")

    # Clone repository (FULL CLONE to get all history)
    if not repo_cache_dir.exists():
        if not check_disk_space(work_dir, required_gb=3.0):
            print(f"    [SKIP] Insufficient disk space")
            return None
        print(f"    -> Cloning full repository...")
        # Use --single-branch to avoid cloning all branches, but get full history
        run_cmd(["git", "clone", "--single-branch", repo_url, str(repo_cache_dir)], timeout=300)
        if not (repo_cache_dir / ".git").exists():
            print(f"    [ERROR] Clone failed")
            shutil.rmtree(repo_cache_dir, ignore_errors=True)
            return None
    
    # Verify commit exists
    verify_sha = run_cmd(["git", "cat-file", "-e", sha], cwd=repo_cache_dir)
    if not verify_sha:  # cat-file -e returns empty on success
        # Try fetching directly
        run_cmd(["git", "fetch", "origin", sha], cwd=repo_cache_dir, timeout=120)
    
    # Get parent commit info
    parent_out = run_cmd(["git", "cat-file", "-p", sha], cwd=repo_cache_dir)
    if not parent_out:
        print(f"    [ERROR] Commit {sha[:8]} not accessible")
        return None
        
    parent_match = re.search(r'parent\s([a-f0-9]{40})', parent_out)
    if not parent_match:
        print(f"    [ERROR] No parent commit found")
        return None
        
    p_sha = parent_match.group(1)

    # Get diff
    diff_out = run_cmd(["git", "diff", p_sha, sha], cwd=repo_cache_dir)
    if not diff_out:
        print(f"    [ERROR] Could not get diff")
        return None
    
    # Parse diff to find C/C++ file
    target_file = None
    file_header_re = re.compile(r'^--- a/(.*\.(?:c|cpp|cc|cxx|h|hpp))$', re.MULTILINE)
    matches = file_header_re.findall(diff_out)
    if matches:
        target_file = matches[0]
    
    if not target_file:
        print(f"    [SKIP] No C/C++ files in diff")
        return None

    # Extract line number
    target_line = None
    hunk_re = re.compile(r'^@@ -(\d+)(?:,\d+)? \+(\d+)')
    for match in hunk_re.finditer(diff_out):
        target_line = int(match.group(2))
        break
    
    if not target_line:
        print(f"    [ERROR] Could not extract line number")
        return None

    # Checkout and extract
    run_cmd(["git", "checkout", "-f", p_sha], cwd=repo_cache_dir)
    
    full_file_path = repo_cache_dir / target_file
    if not full_file_path.exists():
        print(f"    [ERROR] File not found at {target_file}")
        return None
        
    pre_patch_code = full_file_path.read_text(errors='ignore')

    vuln_func_info = find_vulnerable_function(target_file, pre_patch_code, target_line)
    if not vuln_func_info:
        print(f"    [ERROR] Could not find function at line {target_line}")
        return None

    print(f"    -> Found function: '{vuln_func_info['name']}'")
    graph = RepoContextGraph(repo_cache_dir)
    
    # Collect context
    patch_complexity = analyze_patch_complexity(diff_out)
    vuln_type = infer_vuln_type(diff_out, vuln_func_info["body"])
    commit_msg = extract_commit_message(repo_cache_dir, sha)
    intermediate_commits = get_intermediate_commits(repo_cache_dir, p_sha, target_file, max_commits=3)
    conditionals = detect_conditional_compilation(vuln_func_info["body"])
    distractors = categorize_distractors(graph, vuln_func_info, count_per_level=2)
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
        "repo": repo_key,
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

# --- Main Execution ---
def main():
    github_token = os.getenv("GITHUB_TOKEN")
    
    if not github_token:
        print("[!] Warning: GITHUB_TOKEN not set. Set it for better API rate limits: export GITHUB_TOKEN=your_token\n")
    
    base_dir = Path("./vuln_benchmark_builder")
    base_dir.mkdir(exist_ok=True)
    
    cve_repo_dir = base_dir / "cvelistv5"
    output_file = base_dir / "hard_vuln_benchmark.json"
    
    if not cve_repo_dir.exists():
        print("[*] Cloning CVE list repository...")
        run_cmd(["git", "clone", "--depth", "1", "--filter=blob:none", "--sparse", "https://github.com/CVEProject/cvelistv5.git", str(cve_repo_dir)])
        run_cmd(["git", "sparse-checkout", "set", "cves/2026"], cwd=cve_repo_dir)

    cve_paths = list((cve_repo_dir / "cves" / "2026").glob("**/*.json"))
    print(f"[*] Found {len(cve_paths)} CVE JSON files to scan.")
    print(f"[*] Disk available: {get_disk_usage(base_dir)['free_gb']:.1f} GB\n")
    
    random.shuffle(cve_paths)

    dataset = []
    limit = 30  
    
    for idx, path in enumerate(cve_paths):
        if len(dataset) >= limit:
            break
        
        disk_info = get_disk_usage(base_dir)
        print(f"[*] Progress: {len(dataset)}/{limit} | Disk: {disk_info['free_gb']:.1f} GB free | Scanning {idx}/{len(cve_paths)}", end="\r")
        
        try:
            record = process_single_cve(path, base_dir, github_token)
            if record:
                dataset.append(record)
                print(f"[+] Record {len(dataset)}/{limit}: {record['cve_id']:<15} | {record['metadata']['vulnerability_type']:<20}")
                # Clean up repo after successful extraction
                repo_dir = base_dir / f"{record['repo'].split('/')[0]}_{record['repo'].split('/')[1]}"
                if repo_dir.exists():
                    shutil.rmtree(repo_dir, ignore_errors=True)
        except Exception as e:
            continue

    # Save output
    with open(output_file, 'w') as out:
        json.dump(dataset, out, indent=2)
    
    disk_info = get_disk_usage(base_dir)
    print(f"\n[✓] Done! Saved {len(dataset)} records to {output_file.resolve()}")
    print(f"[✓] Final disk: {disk_info['free_gb']:.1f} GB free")

if __name__ == "__main__":
    main()
