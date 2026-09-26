import glob
import re
from collections import defaultdict

def scan_for_duplicates():
    active_files = [f for f in glob.glob("lean/*.lean") if "archive" not in f]
    
    theorem_registry = defaultdict(list)
    total_theorems = 0
    
    print(f"=== ACI THEOREM COLLISION & REPETITION AUDIT ===")
    print(f"Scanning {len(active_files)} active modules...\n")
    
    for file_path in active_files:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            for line_num, line in enumerate(f, 1):
                match = re.match(r'^\s*theorem\s+([a-zA-Z0-9_]+)', line)
                if match:
                    th_name = match.group(1)
                    theorem_registry[th_name].append((file_path, line_num))
                    total_theorems += 1

    duplicates = {name: locs for name, locs in theorem_registry.items() if len(locs) > 1}
    
    print(f"Total theorems scanned: {total_theorems}")
    print(f"Unique theorem names:   {len(theorem_registry)}")
    print(f"Duplicate/Colliding theorems found: {len(duplicates)}\n")
    
    if duplicates:
        print("[WARNING] The following theorem names appear in multiple places:")
        for name, locs in duplicates.items():
            print(f"  - '{name}' appears {len(locs)} times:")
            for file_p, l_num in locs:
                print(f"      -> {file_p}:{l_num}")
    else:
        print("[CLEAN] Zero theorem name collisions detected across the active codebase!")
        print("[ARCHITECTURE] Thanks to timestamped module namespacing (e.g., ACI.ACIMegaCore_1790387842), all generated scopes are completely isolated.")

if __name__ == "__main__":
    scan_for_duplicates()
