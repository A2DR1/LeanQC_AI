import json
import random
import os

PROJECT_ROOT = os.path.abspath(
    os.path.join(os.path.dirname(__file__), "..")
)

F2F_FILE_PATH = os.path.join(
    PROJECT_ROOT,
    "testbench",
    "Putnam",
    "putnam.json"
)

def readPutnamJson(file_path):
    """Read the full putnam.json file."""
    with open(file_path, 'r') as f:
        data = json.load(f)
    return data


def readPutnam(
    file_path=F2F_FILE_PATH,
    limit=100,
    randomize=False,
    include_solution=True
):
    """
    Reads Putnam problems and returns a list of informal problem strings.

    If include_solution=True and an informal_solution exists (not 'None.'),
    append it as an imperative sentence so the task becomes declarative.
    """

    data = readPutnamJson(file_path)

    if randomize:
        random.shuffle(data)

    data = data[:limit]

    informal_statements = []

    for entry in data:
        stmt = entry["informal_statement"].strip()

        sol = entry.get("informal_solution", None)
        if (
            include_solution
            and sol
            and sol.strip().lower() not in {"none", "none."}
        ):
            # Standardize the format
            stmt = stmt + " " + sol.strip()

        informal_statements.append(stmt)

    return informal_statements


if __name__ == "__main__":
    problems = readPutnam(limit=100, randomize=True)
    print(f"Total Putnam problems read: {len(problems)}")
    print()
    print(problems[0])