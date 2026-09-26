import os, glob, re

print(f"{'Module Name':<35} | {'Size (KB)':<10} | {'Theorems':<10}")
print("-" * 61)

for f in sorted(glob.glob("**/*.lean", recursive=True)):
    if ".lake" in f or "lake-pack" in f:
        continue
    try:
        size_kb = round(os.path.getsize(f) / 1024, 2)
        with open(f, "r", encoding="utf-8", errors="ignore") as file:
            content = file.read()
        theorems = len(re.findall(r"\b(theorem|lemma|axiom)\b", content))
        print(f"{os.path.basename(f):<35} | {size_kb:<10} | {theorems:<10}")
    except Exception:
        pass
