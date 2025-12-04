import subprocess
import tempfile
import os
from pathlib import Path

def check_lean_code(code: str, project_path: str):
    # write temporary file
    with open(Path(project_path)/"TmpCheck.lean", "w") as f:
        f.write(code)

    result = subprocess.run(
        ["lake", "env", "lean", "--json", "TmpCheck.lean"],
        cwd=project_path,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )

    # Lean returns 0 exit code if syntactically correct
    ok = (result.returncode == 0)

    return ok, result.stdout + result.stderr
