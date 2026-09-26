import os
import glob
import json

def purge_and_resync():
    print("=" * 65)
    print(" LEGACY PURGE & ECOSYSTEM RESYNCHRONIZATION")
    print("=" * 65)
    
    archive_dir = "lean/archive"
    os.makedirs(archive_dir, exist_ok=True)
    
    # Files that have a v2 equivalent and should be retired from active root
    retire_targets = [
        "lean/ACICorpusCore_1790386130.lean",
        "lean/ACICorpusCore_1790386473.lean",
        "lean/ACIFormalCore.lean",
        "lean/ACIRecursiveCore_1790387036.lean",
        "lean/ACISignedCore_1790385282.lean",
        "lean/ACISignedCore_1790385887.lean",
        "lean/ACISynthesisCore_1790384450.lean"
    ]
    
    retired_count = 0
    for target in retire_targets:
        if os.path.exists(target):
            filename = os.path.basename(target)
            dest = os.path.join(archive_dir, filename)
            # Move to archive if not already there
            if not os.path.exists(dest):
                os.rename(target, dest)
            else:
                os.remove(target)
            print(f"  [RETIRED] Moved {filename} to archive.")
            retired_count += 1
            
    print(f"\nSuccessfully archived {retired_count} legacy base files.")
    
    # Re-scan active lean files for manifest update
    active_files = sorted([
        f for f in glob.glob("lean/*.lean") 
        if "ACIMasterCorpus" not in f and "archive" not in f
    ])
    
    manifest_path = "python_core/verified_modules.json"
    manifest_data = {
        "verified_list": active_files,
        "total_active_modules": len(active_files)
    }
    
    with open(manifest_path, 'w') as f:
        json.dump(manifest_data, f, indent=2)
        
    print(f"[MANIFEST] Updated with {len(active_files)} active v2/mega modules.")
    print("=" * 65)

if __name__ == "__main__":
    purge_and_resync()
