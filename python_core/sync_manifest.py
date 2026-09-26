import json
import glob
import os

def update_manifest():
    manifest_path = "python_core/verified_modules.json"
    os.makedirs("python_core", exist_ok=True)
    
    # Grab all active active v2 and mega core files
    active_files = sorted([
        f for f in glob.glob("lean/*.lean") 
        if "ACIMasterCorpus" not in f and "archive" not in f
    ])
    
    manifest_data = {
        "verified_list": active_files,
        "total_active_modules": len(active_files)
    }
    
    with open(manifest_path, 'w') as f:
        json.dump(manifest_data, f, indent=2)
        
    print(f"[MANIFEST SYNC] Successfully locked {len(active_files)} active modules into {manifest_path}:")
    for file in active_files:
        print(f"  - {file}")

if __name__ == "__main__":
    update_manifest()
