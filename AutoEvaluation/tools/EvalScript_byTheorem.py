import subprocess
import re
from pathlib import Path

# --- CONFIG ---
LEAN_CMD = ["lake", "env", "lean"]  # or ["lake", "env", "lean"] if using lake environment
ROOT_DIR = "Generated"  # Folder where your generated .lean files are stored

# --- REGEX PATTERNS ---
theorem_pattern = re.compile(r"theorem\s+([A-Za-z0-9_]+)")
error_pattern = re.compile(
    r'(?P<file>.+?):(?P<line>\d+):(?P<col>\d+): error: (?P<msg>.+)'
)

def extract_theorems(file_text):
    """Extract theorem names with their line numbers."""
    theorems = []
    for i, line in enumerate(file_text.splitlines(), start=1):
        match = theorem_pattern.search(line)
        if match:
            theorems.append({"name": match.group(1), "line": i})
    return theorems

def run_lean(file_path):
    """Run Lean and capture errors."""
    result = subprocess.run(
        LEAN_CMD + [file_path],
        capture_output=True,
        text=True
    )
    output = result.stderr.strip() or result.stdout.strip()
    errors = []
    for m in error_pattern.finditer(output):
        errors.append({
            "file": m.group("file"),
            "line": int(m.group("line")),
            "col": int(m.group("col")),
            "msg": m.group("msg").strip()
        })
    return errors

def map_errors_to_theorems(file_text, errors):
    """Map each error to its nearest preceding theorem."""
    theorems = extract_theorems(file_text)
    results = []
    for err in errors:
        line = err["line"]
        nearest = None
        for th in theorems:
            if th["line"] <= line:
                nearest = th["name"]
            else:
                break
        results.append({
            "theorem": nearest or "(no theorem found)",
            "line": line,
            "msg": err["msg"]
        })
    return results

def check_file(file_path):
    """Check one Lean file and map errors to theorems."""
    print(f"🔍 Checking {file_path}...")
    text = Path(file_path).read_text(encoding="utf-8")
    errors = run_lean(file_path)
    mapped = map_errors_to_theorems(text, errors)

    if not mapped:
        print("✅ No errors found.\n")
        return []

    print("❌ Errors:")
    for e in mapped:
        print(f"  • {e['theorem']} (line {e['line']}): {e['msg']}")
    print()
    return mapped

def main():
    all_results = []
    for lean_file in Path(ROOT_DIR).rglob("*.lean"):
        all_results.extend(check_file(lean_file))

    # Summary
    print("📊 Summary:")
    print(f"  Total errors: {len(all_results)}")
    if all_results:
        for e in all_results[:10]:
            print(f"  - {e['theorem']}: {e['msg']}")

if __name__ == "__main__":
    main()