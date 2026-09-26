import os

def categorize_repository():
    print("=" * 75)
    print(" REPOSITORY COMPOSITION & CATEGORIZATION AUDIT")
    print("=" * 75)
    
    categories = {
        "Lean Mathematical Modules (.lean)": {"files": 0, "lines": 0},
        "System & Runtime Intelligence (.py, .sh)": {"files": 0, "lines": 0},
        "Audit Reports & Text Dumps (.txt, .tsv, .md)": {"files": 0, "lines": 0},
        "Build Artifacts, CMake & Cache (.cmake, CMakeCache, etc.)": {"files": 0, "lines": 0},
        "Configs, Logs & Other": {"files": 0, "lines": 0}
    }
    
    for root, dirs, files in os.walk("."):
        if ".git" in root or ".lake" in root:
            continue
            
        for file in files:
            full_path = os.path.join(root, file).replace("./", "")
            
            # Count lines safely
            line_count = 0
            try:
                with open(full_path, 'r', encoding='utf-8', errors='ignore') as f:
                    for _ in f:
                        line_count += 1
            except Exception:
                line_count = 0
                
            # Bucket classification
            if file.endswith(".lean"):
                categories["Lean Mathematical Modules (.lean)"]["files"] += 1
                categories["Lean Mathematical Modules (.lean)"]["lines"] += line_count
            elif file.endswith((".py", ".sh")):
                categories["System & Runtime Intelligence (.py, .sh)"]["files"] += 1
                categories["System & Runtime Intelligence (.py, .sh)"]["lines"] += line_count
            elif file.endswith((".txt", ".tsv", ".md")) or "ACI_AUDIT" in full_path:
                categories["Audit Reports & Text Dumps (.txt, .tsv, .md)"]["files"] += 1
                categories["Audit Reports & Text Dumps (.txt, .tsv, .md)"]["lines"] += line_count
            elif "CMake" in root or "CMakeFiles" in root or file.endswith((".cmake", "CMakeCache.txt", ".yaml")) or "cache" in file.lower():
                categories["Build Artifacts, CMake & Cache (.cmake, CMakeCache, etc.)"]["files"] += 1
                categories["Build Artifacts, CMake & Cache (.cmake, CMakeCache, etc.)"]["lines"] += line_count
            else:
                categories["Configs, Logs & Other"]["files"] += 1
                categories["Configs, Logs & Other"]["lines"] += line_count

    total_files = sum(v["files"] for v in categories.values())
    total_lines = sum(v["lines"] for v in categories.values())
    
    print(f"{'Ecosystem Component':<52} | {'Files':<6} | {'Lines':<10} | {'Share':<6}")
    print("-" * 82)
    for cat, data in categories.items():
        share = (data["lines"] / max(1, total_lines)) * 100
        print(f"{cat:<52} | {data['files']:<6} | {data['lines']:<10,} | {share:>5.1f}%")
    print("-" * 82)
    print(f"{'GRAND TOTAL':<52} | {total_files:<6} | {total_lines:<10,}")
    print("=" * 75)

if __name__ == "__main__":
    categorize_repository()
