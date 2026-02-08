import os 
import json
from .handler import handler

PROJECT_ROOT = os.path.abspath(
    os.path.join(os.path.dirname(__file__), "..")
)

F2F_TEST_PATH = os.path.join(
    PROJECT_ROOT,
    "testbench",
    "ProofNet",
    "test.jsonl"
)

class ProofNetHandler(handler):
    def __init__(self):
        super().__init__()

    def read(self, inputPath:str = F2F_TEST_PATH, limit: int = 100, randomize: bool = False) -> list[str]:
        return self.readFile(
            file_path=inputPath,
            limit=limit,
            randomize=randomize
        )

    def readJsonl(self, file_path):
        data_list = []
        with open(file_path, 'r') as f:
            for line in f:
                data = json.loads(line)
                data_list.append(data['nl_statement'])
        return data_list 
    
    def readFile(self, file_path, limit=100, randomize=False):
        all_statements = self.readJsonl(file_path)

        if randomize:
            import random
            random.shuffle(all_statements)

        return all_statements[:limit]

if __name__ == "__main__":
    proofnethendler = ProofNetHandler()
    informal_statements = proofnethendler.read()
    print(f"Total informal statements read: {len(informal_statements)}")
    print(informal_statements[0])

