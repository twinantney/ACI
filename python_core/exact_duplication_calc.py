import os
from collections import defaultdict

def calculate_duplication():
    corpus_path = "ACIMasterCorpus.lean"
    if not os.path.exists(corpus_path):
        corpus_path = "lean/ACIMasterCorpus.lean"
        
    if not os.path.exists(corpus_path):
        print(f"[ERROR] Master Corpus not found.")
        return

    with open(corpus_path, 'r', encoding='utf-8', errors='ignore') as f:
        lines = f.readlines()

    total_lines = len(lines)
    line_frequency = defaultdict(int)
    
    # Track non-empty, non-comment lines for structural analysis
    active_lines_count = 0
    for line in lines:
        stripped = line.strip()
        if stripped and not stripped.startswith("--"):
            line_frequency[stripped] += 1
            active_lines_count += 1

    # Calculate exact duplicates vs unique lines
    unique_active_lines = len(line_frequency)
    duplicated_line_instances = sum(count for line, count in line_frequency.items() if count > 1)
    purely_unique_lines = sum(1 for line, count in line_frequency.items() if count == 1)

    duplication_percentage = (duplicated_line_instances / max(1, active_lines_count)) * 100

    print("=" * 65)
    print(" ACIMasterCorpus EXACT LINE DEDUPLICATION AUDIT")
    print("=" * 65)
    print(f"  - Total Corpus Lines (including whitespace/comments): {total_lines:,}")
    print(f"  - Total Active Code Lines (excluding comments):      {active_lines_count:,}")
    print(f"  - Globally Unique Code Lines:                       {unique_active_lines:,}")
    print(f"  - Lines Appearing Multiple Times (Template Overlap):  {duplicated_line_instances:,}")
    print(f"  - Purely Unique Code Lines (Appears 1 time):        {purely_unique_lines:,}")
    print(f"  - Exact Structural Redundancy Ratio:                {duplication_percentage:.1f}%")
    print("=" * 65)

if __name__ == "__main__":
    calculate_duplication()
