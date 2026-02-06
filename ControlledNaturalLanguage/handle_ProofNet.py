import json

filepath = "ProofNet/test.jsonl"

def read_jsonl(file_path, limit=100):
    informal_statements = []
    with open(file_path, "r") as f:
        for i, line in enumerate(f):
            if i >= limit:
                break
            informal_statements.append(json.loads(line)['nl_statement'])
    
    return informal_statements

    
def readFolder(folder_path, limit=100):
    # just folling the convention in handle_miniF2F.py
    return read_jsonl(folder_path, limit=limit)

if __name__ == "__main__":
    informal_statements = readFolder(filepath, limit=100)
    print(f"Total informal statements read: {len(informal_statements)}")
    for i, statement in enumerate(informal_statements):
        print(f"Statement {i+1}:\n{statement}\n")