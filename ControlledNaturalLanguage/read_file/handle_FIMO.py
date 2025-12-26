import os
import json
import random
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]  # .../ControlledNaturalLanguage
FIMO_DIR = PROJECT_ROOT / "testbench" / "FIMO"

def _read_json(file_path: Path) -> dict:
    with open(file_path, "r", encoding="utf-8") as f:
        return json.load(f)

def readFolder_fimo(
    folder_path: str | Path = FIMO_DIR,
    limit: int = 100,
    randomize: bool = False,
    include_proof: bool = False,
    proof_prefix: str = "Proof (informal): "
) -> list[str]:
    """
    Reads FIMO problems from per-problem JSON files and returns a list of strings.

    - include_proof=False (default): returns only `informal_statement`
    - include_proof=True: appends informal_proof as extra text (optional experiment)
    """
    folder_path = Path(folder_path)
    if not folder_path.exists():
        raise FileNotFoundError(f"FIMO folder not found: {folder_path}")

    json_files = [p for p in folder_path.iterdir() if p.suffix == ".json"]
    if randomize:
        random.shuffle(json_files)
    else:
        json_files.sort()

    json_files = json_files[:limit]
    out: list[str] = []

    for p in json_files:
        obj = _read_json(p)
        stmt = (obj.get("informal_statement") or "").strip()
        if not stmt:
            continue

        if include_proof:
            proof = (obj.get("informal_proof") or "").strip()
            if proof:
                stmt = stmt + "\n\n" + proof_prefix + proof

        out.append(stmt)

    return out


if __name__ == "__main__":
    problems = readFolder_fimo(limit=5, randomize=True)
    print(len(problems))
    print(problems[0])