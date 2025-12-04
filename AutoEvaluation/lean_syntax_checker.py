#!/usr/bin/env python3

"""
This checker works but is extremely slow
"""
import json
import subprocess
import tempfile
from pathlib import Path
from typing import List, Optional, Tuple
import re


class LeanSyntaxError:
    def __init__(self, file: str, line: int, col: int, msg: str):
        self.file = file
        self.line = line
        self.col = col
        self.msg = msg

    def __str__(self):
        return f"{self.file}:{self.line}:{self.col}: {self.msg}"


def _run_lean(path: Path, project_root: Optional[Path]) -> Tuple[bool, str, str]:
    cwd = project_root if project_root else path.parent
    cmd = ["lake", "env", "lean", "--json", str(path)]

    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            text=True,
            capture_output=True
        )
    except FileNotFoundError as e:
        return False, "", str(e)

    ok = proc.returncode == 0
    return ok, proc.stdout, proc.stderr


def _extract_json_lines(raw_output: str):
    """
    Extract JSON objects printed line-by-line.
    Lean prints exactly one JSON object per compiler message.
    """
    objs = []
    for line in raw_output.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            objs.append(json.loads(line))
        except Exception:
            pass
    return objs


def _parse_diagnostics(stdout: str, stderr: str) -> List[LeanSyntaxError]:
    errors: List[LeanSyntaxError] = []

    # -----------
    # Case 1: JSON messages as top-level objects
    # Example (your output):
    #
    # {"data":"type mismatch ...", "pos": { ... }, "severity":"error", "fileName": "..."}
    # -----------
    objs = _extract_json_lines(stdout) + _extract_json_lines(stderr)

    for obj in objs:
        if obj.get("severity") == "error":
            pos = obj.get("pos", {})
            msg = obj.get("data", obj.get("caption", "error"))

            errors.append(
                LeanSyntaxError(
                    file=obj.get("fileName", "<unknown>"),
                    line=pos.get("line", 0),
                    col=pos.get("column", 0),
                    msg=msg.replace("\n", " ")  # make single-line
                )
            )

    if errors:
        return errors

    # -----------
    # Case 2: Legacy stderr-only messages fallback
    # -----------
    pattern = re.compile(r"^(.*?\.lean):(\d+):(\d+): (.*)$")

    for line in stderr.splitlines():
        match = pattern.match(line.strip())
        if match:
            file, line, col, msg = match.groups()
            errors.append(
                LeanSyntaxError(
                    file=file,
                    line=int(line),
                    col=int(col),
                    msg=msg
                )
            )

    return errors


def check_lean_file(path: str, project_root: Optional[str] = None):
    p = Path(path).resolve()
    root = Path(project_root).resolve() if project_root else None

    ok, out, err = _run_lean(p, root)
    errors = _parse_diagnostics(out, err)

    return ok, errors, out, err


def check_lean_code(code: str, project_root: Optional[str] = None):
    import textwrap
    code = textwrap.dedent(code)

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpfile = Path(tmpdir) / "tmp.lean"
        tmpfile.write_text(code)

        ok, out, err = _run_lean(tmpfile, Path(project_root) if project_root else None)
        errors = _parse_diagnostics(out, err)

        return ok, errors, out, err


if __name__ == "__main__":
    print("=== BAD CODE TEST ===")
    bad_code = """
def foo : Nat := "hello"
"""
    ok, errors, _, _ = check_lean_code(bad_code)
    print("OK:", ok)
    print("Errors:")
    for e in errors:
        print("  ", e)

    print("\n=== GOOD CODE TEST ===")
    good_code = """
def foo (n : Nat) := n + 1
"""
    ok, errors, _, _ = check_lean_code(good_code)
    print("OK:", ok)
    print("Errors:", errors)

    print("\n=== MATHLIB CODE TEST ===")

    good_code = r"""
import Mathlib

theorem myFact : True := by
  trivial
"""
    ok, errors, _, _ = check_lean_code(
        good_code,
        project_root="/Users/austinshen/Documents/Umich/Research/LeanQC_AI/AutoEvaluation" )
    print("OK:", ok)
    print("Errors:", errors)
    print("Errors:")
    for e in errors:
        print(e)