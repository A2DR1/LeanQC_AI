import os 
import json

folder_path = "miniF2F/informal/test"

def readJson(file_path):
    import json
    with open(file_path, 'r') as f:
        data = json.load(f)
    return data

def readFolder(folder_path, limit=100):
    data_list = []
    for i, filename in enumerate(os.listdir(folder_path)):
        # Limit to first 100 files for testing
        if i >= limit:
            break
        if filename.endswith(".json"):
            file_path = os.path.join(folder_path, filename)
            print(f"Reading file: {file_path}")
            data = readJson(file_path)
            data_list.append(data['informal_statement'])
    return data_list

if __name__ == "__main__":

    informal_statements = readFolder(folder_path)
    print(f"Total informal statements read: {len(informal_statements)}")
    print(informal_statements[0])

