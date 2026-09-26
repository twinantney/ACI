import json
import re
from collections import defaultdict

def strict_audit():
    manifest_path = "python_core/verified_modules.json"
    
    try:
        with open(manifest_path, 'r') as f:
            manifest = json.load(f)
            active_files = manifest.get("verified_list", [])
    except Exception as e:
        print(f"[ERROR] Could not load manifest: {e}")
        return

    print("=" * 65)
    print(" MANIFEST-STRICT ECOSYSTEM AUDIT (ACTIVE 15 MODULES ONLY)")
    print("=" * 65)
    print(f"Auditing exactly {len(active_files)} files declared in manifest:\n")
    
    total_lines = 0
    total_theorems = 0
    theorem_registry = defaultdict(list)
    file_stats = []
    
    for file_path in active_files:
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
            print(f"[WARNING] File not found or unreadable: {file_path}")
            continue
            
        total_lines += lines
        file_stats.append((file_path, lines, file_th_count))

    print(f"{'Active Module File':<45} | {'Lines':<7} | {'Theorems':<8}")
    print("-" * 65)
    for path, lns, ths in file_stats:
        print(f"{path:<45} | {lns:<7} | {ths:<8}")
    print("-" * 65)
    print(f"{'TOTAL MANIFEST CORPUS':<45} | {total_lines:<7} | {total_theorems:<8}")

    # Check for true cross-file duplicates strictly within the active 15
    shared_theorems = {name: paths for name, paths in theorem_registry.items() if len(set(paths)) > 1}
    
    print(f"\n[STRICT REDUNDANCY METRICS]:")
    print(f"  - Total Unique Theorem Signatures : {len(theorem_registry)}")
    print(f"  - Theorems Shared Across Modules  : {len(shared_theorems)}")
    
    if shared_theorems:
        print(f"  - Note: Shared items are expected between historical v2 wrappers and their bases.")
        
    print("=" * 65)

if __name__ == "__main__":
    strict_audit()
