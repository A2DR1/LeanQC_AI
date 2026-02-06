import json
import random
import os
from .handler import handler

PROJECT_ROOT = os.path.abspath(
    os.path.join(os.path.dirname(__file__), "..")
)

F2F_FILE_PATH = os.path.join(
    PROJECT_ROOT,
    "testbench",
    "Putnam",
    "putnam.json"
)

class PutnamHandler(handler):
    def __init__(self):
        super().__init__()

    def read(self, inputPath:str = F2F_FILE_PATH, limit: int = 100, randomize: bool = False, include_solution = False) -> list[str]:
        return self.readPutnam(
            file_path=inputPath,
            limit=limit,
            randomize=randomize,
            include_solution=include_solution
        )

    def readPutnamJson(self,file_path):
        """Read the full putnam.json file."""
        with open(file_path, 'r') as f:
            data = json.load(f)
        return data


    def readPutnam(
        self,
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

        data = self.readPutnamJson(file_path)

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
    putnam_handler = PutnamHandler()
    problems = putnam_handler.read(limit=100, randomize=True)
    print(f"Total Putnam problems read: {len(problems)}")
    print("Example problem:")
    print(problems[0])