import os 
import json

PROJECT_ROOT = os.path.abspath(
    os.path.join(os.path.dirname(__file__), "..")
)

F2F_TEST_PATH = os.path.join(
    PROJECT_ROOT,
    "testbench",
    "MiniF2F",
    "test"
)

def readJson(file_path):
    import json
    with open(file_path, 'r') as f:
        data = json.load(f)
    return data

def readFolder(folder_path=F2F_TEST_PATH, limit=100, randomize=False):
    data_list = []
    if randomize:
        import random
        all_filenames = [filename for filename in os.listdir(folder_path) if filename.endswith(".json")]
        random.shuffle(all_filenames)
        selected_filenames = all_filenames[:limit]
        for filename in selected_filenames:
            file_path = os.path.join(folder_path, filename)
            data = readJson(file_path)
            data_list.append(data['informal_statement'])
    else:
        for i, filename in enumerate(os.listdir(folder_path)):
            # Limit to first 100 files for testing
            if i >= limit:
                break
            if filename.endswith(".json"):
                file_path = os.path.join(folder_path, filename)
                data = readJson(file_path)
                data_list.append(data['informal_statement'])
    return data_list

if __name__ == "__main__":

    informal_statements = readFolder()
    print(f"Total informal statements read: {len(informal_statements)}")
    print(informal_statements[0])

