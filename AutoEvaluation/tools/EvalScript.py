# tools/check_lean_files.py
import subprocess
import os

# Folder containing generated Lean files
GENERATED_DIR = "Generated"

def check_lean_file(filepath):
    """Run Lean on a single file and capture output."""
    result = subprocess.run(["lake", "env", "lean", filepath])
    success = (result.returncode == 0)
    return success, result.stdout, result.stderr

def main():
    print("🔍 Checking generated Lean files...\n")
    lean_files = [os.path.join(GENERATED_DIR, f)
                  for f in os.listdir(GENERATED_DIR)
                  if f.endswith(".lean") and not f.startswith("_")]

    total = len(lean_files)
    passed = 0

    for filepath in lean_files:
        print(f"▶ Checking {filepath}...")
        success, out, err = check_lean_file(filepath)
        if success:
            print(f"✅ Passed: {filepath}\n")
            passed += 1
        else:
            print(f"❌ Failed: {filepath}\n{err}\n")

    print("📊 Summary:")
    print(f"  {passed}/{total} files compiled successfully.\n")

if __name__ == "__main__":
    main()