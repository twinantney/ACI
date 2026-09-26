import os

def full_directory_inventory():
    print("=" * 85)
    print(" FULL REPOSITORY INVENTORY (UNRESTRICTED ENTIRE DIRECTORY)")
    print("=" * 85)
    
    all_files = []
    for root, dirs, files in os.walk("."):
        # Skip hidden system folders like git or lake build caches
        if ".git" in root or ".lake" in root or "__pycache__" in root or ".pytest_cache" in root:
            continue
        for file in files:
            full_path = os.path.join(root, file).replace("./", "")
            all_files.append(full_path)
            
    all_files = sorted(all_files)
    
    print(f"{'No.':<6} | {'File Path':<55} | {'Size (KB)':<10} | {'Lines':<8}")
    print("-" * 85)
    
    total_lines = 0
    total_bytes = 0
    file_count = 0
    
    for idx, file_path in enumerate(all_files, 1):
        if not os.path.exists(file_path):
            continue
        
        try:
            file_size_bytes = os.path.getsize(file_path)
        except Exception:
            file_size_bytes = 0
            
        file_size_kb = file_size_bytes / 1024.0
        total_bytes += file_size_bytes
        
        line_count = 0
        # Count lines for text/code/config files
        if file_path.endswith(('.lean', '.py', '.json', '.md', '.txt', '.sh', '.yaml', '.yml')) or '.' not in file_path:
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    for _ in f:
                        line_count += 1
            except Exception:
                line_count = 0
        
        total_lines += line_count
        file_count += 1
        
        print(f"{idx:<6} | {file_path:<55} | {file_size_kb:>8.1f} | {line_count:<8}")
        
    print("-" * 85)
    print(f"GRAND TOTALS: {file_count} files | {(total_bytes / (1024*1024)):.2f} MB | {total_lines:,} total lines")
    print("=" * 85)

if __name__ == "__main__":
    full_directory_inventory()
