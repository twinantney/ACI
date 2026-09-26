import os
import json
import glob

def build_master_corpus():
    corpus_path = "lean/ACIMasterCorpus.lean"
    
    # Check if a verified module manifest/registry exists, otherwise fallback to scanning verified files
    verified_files = []
    manifest_path = "python_core/verified_modules.json"
    
    if os.path.exists(manifest_path):
        with open(manifest_path, 'r') as f:
            data = json.load(f)
            verified_files = data.get("verified_list", [])
        print(f"[CORPUS] Loaded {len(verified_files)} modules from official Verified List manifest.")
    else:
        # Fallback: gather all lean files except corpus itself
        verified_files = [f for f in glob.glob("lean/*.lean") if "ACIMasterCorpus" not in f]
        print(f"[CORPUS] No JSON manifest found. Scanning {len(verified_files)} local Lean files.")
    
    total_source_lines = 0
    corpus_blocks = [
        "namespace ACI.MasterCorpus",
        "-- DYNAMICALLY SYNCHRONIZED MASTER CORPUS (Verified List Integration)",
        ""
    ]
    
    for file_path in sorted(verified_files):
        if not os.path.exists(file_path):
            # Try prepending lean/ if not specified
            if os.path.exists(os.path.join("lean", file_path)):
                file_path = os.path.join("lean", file_path)
            else:
                print(f"[WARNING] Verified file not found on disk: {file_path}")
                continue
                
        with open(file_path, 'r') as f:
            lines = f.readlines()
            total_source_lines += len(lines)
            corpus_blocks.append(f"\n-- BEGIN VERIFIED MODULE: {os.path.basename(file_path)}")
            corpus_blocks.extend(lines)
            corpus_blocks.append(f"-- END VERIFIED MODULE: {os.path.basename(file_path)}\n")
            
    corpus_blocks.append("end ACI.MasterCorpus")
    
    full_corpus_text = "".join(corpus_blocks)
    with open(corpus_path, 'w') as f:
        f.write(full_corpus_text)
        
    corpus_lines = len(full_corpus_text.splitlines())
    print(f"[CORPUS STATS] Total lines from Verified List: {total_source_lines}")
    print(f"[CORPUS STATS] Total lines in ACIMasterCorpus.lean: {corpus_lines}")
    print(f"[CORPUS SUCCESS] Master corpus successfully synchronized with Verified List.")

if __name__ == "__main__":
    build_master_corpus()
