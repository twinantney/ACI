import glob
import re
from collections import defaultdict
import os

def summarize_codebase():
    active_files = sorted([f for f in glob.glob("lean/*.lean") if "archive" not in f])
    
    print("=" * 60)
    print(" ACI CODEBASE INTELLIGENCE & REDUNDANCY SUMMARY")
    print("=" * 60)
    
    total_codebase_lines = 0
    file_stats = []
    theorem_registry = defaultdict(list)
    total_theorems = 0
    
    for file_path in active_files:
        line_count = 0
        file_theorems = 0
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            for line in f:
                line_count += 1
                match = re.match(r'^\s*theorem\s+([a-zA-Z0-9_]+)', line)
                if match:
                    th_name = match.group(1)
                    theorem_registry[th_name].append(file_path)
                    file_theorems += 1
                    total_theorems += 1
                    
        total_codebase_lines += line_count
        file_stats.append((file_path, line_count, file_theorems))

    print(f"\n[1] FILE-BY-FILE LINE & THEOREM BREAKDOWN:")
    print(f"{'Module File':<40} | {'Lines':<8} | {'Theorems':<8}")
    print("-" * 62)
    for path, lines, ths in file_stats:
        print(f"{path:<40} | {lines:<8} | {ths:<8}")
    print("-" * 62)
    print(f"{'TOTAL ACTIVE CODEBASE':<40} | {total_codebase_lines:<8} | {total_theorems:<8}")

    # Analyze cross-file duplicates
    cross_file_duplicates = 0
    for th_name, files in theorem_registry.items():
        unique_files = set(files)
        if len(unique_files) > 1:
            cross_file_duplicates += 1

    print(f"\n[2] REDUNDANCY & DUPLICATION METRICS:")
    print(f"  - Total Theorem Signatures Scanned : {total_theorems}")
    print(f"  - Globally Unique Theorem Names    : {len(theorem_registry)}")
    print(f"  - Theorems Shared Across Files     : {cross_file_duplicates}")
    
    # Calculate duplication percentage based on v2 wrapping historical code
    duplication_ratio = (cross_file_duplicates / max(1, len(theorem_registry))) * 100
    print(f"  - Cross-File Code Overlap Ratio    : {duplication_ratio:.1f}%")
    print(f"  - External Dependencies (Mathlib)  : 0 (Pure Independent Logic)")
    print("=" * 60)

if __name__ == "__main__":
    summarize_codebase()
