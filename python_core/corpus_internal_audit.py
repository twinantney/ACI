import re
from collections import defaultdict
import os

def audit_corpus():
    # Locate the Master Corpus file
    corpus_path = "ACIMasterCorpus.lean"
    if not os.path.exists(corpus_path):
        corpus_path = "lean/ACIMasterCorpus.lean"
        
    if not os.path.exists(corpus_path):
        print(f"[ERROR] Could not locate Master Corpus file on disk.")
        return

    print("=" * 65)
    print(f" MASTER CORPUS INTERNAL AUDIT: {corpus_path}")
    print("=" * 65)
    
    total_lines = 0
    theorem_registry = defaultdict(list)
    total_theorems = 0
    
    with open(corpus_path, 'r', encoding='utf-8', errors='ignore') as f:
        for line_num, line in enumerate(f, 1):
            total_lines += 1
            match = re.match(r'^\s*theorem\s+([a-zA-Z0-9_]+)', line)
            if match:
                th_name = match.group(1)
                theorem_registry[th_name].append(line_num)
                total_theorems += 1

    # Find internal collisions within the corpus
    internal_duplicates = {name: locs for name, locs in theorem_registry.items() if len(locs) > 1}
    
    print(f"  - Total Master Corpus Lines       : {total_lines:,}")
    print(f"  - Total Theorem Signatures Scanned: {total_theorems:,}")
    print(f"  - Globally Unique Theorem Names   : {len(theorem_registry):,}")
    print(f"  - Internally Duplicated Theorems  : {len(internal_duplicates)}")
    
    if internal_duplicates:
        print(f"\n[NOTICE] Found {len(internal_duplicates)} theorem names reused across different namespaces inside the corpus:")
        for name, locs in list(internal_duplicates.items())[:5]:
            print(f"    * '{name}' appears at lines: {locs}")
        if len(internal_duplicates) > 5:
            print(f"    ... and {len(internal_duplicates) - 5} more.")
    else:
        print("\n[CLEAN] Zero internal theorem name collisions detected in the Master Corpus!")

    print("=" * 65)

if __name__ == "__main__":
    audit_corpus()
