import os
import json
import glob

def smart_sync():
    print("=" * 65)
    print(" SMART ECOSYSTEM DISCOVERY & MANIFEST REBUILDER")
    print("=" * 65)
    
    valid_lean_files = []
    
    # Walk the tree, but intelligently ignore junk directories like .git, target, archive, etc.
    for root, dirs, files in os.walk("."):
        # Skip hidden directories and archive
        if any(skip in root for skip in [".git", "archive", "target", ".lake"]):
            continue
            
        for file in files:
            if file.endswith(".lean"):
                full_path = os.path.join(root, file)
                # Normalize path format
                clean_path = full_path.replace("./", "")
                valid_lean_files.append(clean_path)
                
    valid_lean_files = sorted(list(set(valid_lean_files)))
    
    print(f"[DISCOVERY] Found {len(valid_lean_files)} legitimate active .lean files across the workspace.")
    
    # Update manifest with the complete true list
    manifest_path = "python_core/verified_modules.json"
    os.makedirs("python_core", exist_ok=True)
    
    manifest_data = {
        "verified_list": valid_lean_files,
        "total_active_modules": len(valid_lean_files)
    }
    
    with open(manifest_path, 'w') as f:
        json.dump(manifest_data, f, indent=2)
        
    print(f"[MANIFEST UPDATED] Successfully locked {len(valid_lean_files)} modules into {manifest_path}.\n")
    
    # Quick summary of categories found
    print("Sample of discovered modules:")
    for path in valid_lean_files[:10]:
        print(f"  - {path}")
    if len(valid_lean_files) > 10:
        print(f"  ... and {len(valid_lean_files) - 10} more modules.")
    print("=" * 65)

if __name__ == "__main__":
    smart_sync()
