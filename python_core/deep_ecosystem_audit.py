import os
import re
from collections import defaultdict

def deep_audit():
    # Recursively find ALL .lean files across the entire project repository
    all_lean_files = []
    for root, dirs, files in os.walk("."):
        # Skip git or hidden folders if any
        if ".git" in root:
            continue
        for file in files:
            if file.endswith(".lean"):
                all_lean_files.append(os.path.join(root, file))
                
    all_lean_files = sorted(list(set(all_lean_files)))
    
    print("=" * 70)
    print(" DEEP RECURSIVE ECOSYSTEM AUDIT (ALL MODULES & DIRECTORIES)")
    print("=" * 70)
    print(f"Total .lean files found across project: {len(all_lean_files)}\n")
    
    total_lines = 0
    total_theorems = 0
    theorem_registry = defaultdict(list)
    
    file_stats = []
    
    for file_path in all_lean_files:
        lines = 0
        file_th_count = 0
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                for line in f:
                    lines += 1
                    match = re.match(r'^\s*theorem\s+([a-zA-Z0-9_]+)', line)
                    if match:
                        th_name = match.group(1)
                        theorem_registry[th_name].append(file_path)
                        file_th_count += 1
                        total_theorems += 1
        except Exception as e:
            print(f"[ERROR reading {file_path}] {e}")
            
        total_lines += lines
        file_stats.append((file_path, lines, file_th_count))

    print(f"{'File Path':<55} | {'Lines':<7} | {'Theorems':<8}")
    print("-" * 75)
    for path, lns, ths in file_stats:
        print(f"{path:<55} | {lns:<7} | {ths:<8}")
    print("-" * 75)
    print(f"{'TOTAL ECOSYSTEM CORPUS':<55} | {total_lines:<7} | {total_theorems:<8}")

    # Analyze true cross-file duplicates (ignoring intentional v2 wrapping of its own parent)
    shared_theorems = {name: paths for name, paths in theorem_registry.items() if len(set(paths)) > 1}
    
    print(f"\n[ECOSYSTEM REDUNDANCY METRICS]:")
    print(f"  - Total Unique Theorem Names     : {len(theorem_registry)}")
    print(f"  - Theorems Appearing in >1 File  : {len(shared_theorems)}")
    
    if shared_theorems:
        print(f"  - Sample Shared Theorems (e.g. historical wrappers / Prime Master inclusions):")
        for name, paths in list(shared_theorems.items())[:5]:
            print(f"      * '{name}' shared across: {paths}")

    print("=" * 70)

if __name__ == "__main__":
    deep_audit()
