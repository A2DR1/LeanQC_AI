from CNL_generation import generate_cnl_list, read_cnl_lst, write_cnl_to_file
from FL_generation import generate_write

benchmark = "ProofNet"
CNL_path = f'history/{benchmark}/CNL'
Lean_files_path = f'history/{benchmark}/Lean_files'
NL_FL_pairs_path = f'history/{benchmark}/NL_FL_pairs'

def run_control(folder_path = None):
    if folder_path is None:
        folder_path = input("Folder path: ")

    generate_write(folder_path, name=f"{Lean_files_path}/control.lean", json_output_path=f"{NL_FL_pairs_path}/NL_FL_pairs_control.json")

    print(f"\n✅ Saved NL-FL pairs to {NL_FL_pairs_path}/NL_FL_pairs_control.json")

def run_version(version = None, folder_path = None):
    if version is None:
        version = input("Version: ")

    cnl_statements = generate_cnl_list(folder_path, limit=100, version=version)
    write_cnl_to_file(cnl_statements, filename=f"{CNL_path}/cnl_statements_v{version}.json")

    generate_write(f"{CNL_path}/cnl_statements_v{version}.json", name=f"{Lean_files_path}/Autoformalized_CNL_v{version}.lean", json_output_path=f"{NL_FL_pairs_path}/NL_FL_pairs_CNL_v{version}.json")

    print(f"\n✅ Saved CNL statements to {CNL_path}/cnl_statements_v{version}.json")
    print(f"\n✅ Saved CNL autoformalizations to {Lean_files_path}/Autoformalized_CNL_v{version}.lean")
    print(f"\n✅ Saved NL-FL pairs to {NL_FL_pairs_path}/NL_FL_pairs_CNL_v{version}.json")

def count_corrects(version = None, file_path = None):
    import json

    if version is None and file_path is None:
        version = input("Version: ")

    if file_path is not None:
        with open(file_path, 'r') as f:
            data = json.load(f)
    else:
        with open(f"{NL_FL_pairs_path}/NL_FL_pairs_CNL_v{version}.json", 'r') as f:
            data = json.load(f)
    syntactic_corrects = [entry['is_syntactically_correct'] for entry in data]
    corrects = [entry['is_semantically_correct'] for entry in data if entry['is_syntactically_correct']]

    syntax_accuracy = sum(syntactic_corrects) / len(syntactic_corrects) * 100
    semantic_accuracy = sum(corrects) / len(corrects) * 100

    # show the raw numbers as well
    print(f"Syntactic Correct: {sum(syntactic_corrects)}/{len(syntactic_corrects)}")
    print(f"Semantic Correct: {sum(corrects)}/{len(corrects)}") 
    print(f"\n✅ CNL v{version} - Syntactic Accuracy: {syntax_accuracy:.2f}%, Semantic Accuracy: {semantic_accuracy:.2f}%")
    print(f"Overall Accuracy: {(sum(corrects)/len(data))*100:.2f}%")

def overall_accuracy(version = None, file_path = None):
    import json

    if version is None and file_path is None:
        version = input("Version: ")

    if file_path is not None:
        with open(file_path, 'r') as f:
            data = json.load(f)
    else:
        with open(f"{NL_FL_pairs_path}/NL_FL_pairs_CNL_v{version}.json", 'r') as f:
            data = json.load(f)

    corrects = [entry['is_semantically_correct'] for entry in data if entry['is_syntactically_correct']]

    overall_accuracy = sum(corrects) / len(data) * 100

    print(f"\n✅ CNL v{version} - Overall Accuracy: {overall_accuracy:.2f}%")
    return overall_accuracy

if __name__ == "__main__":
    folder_path = "ProofNet/test.jsonl"
    # run_control(folder_path=folder_path)
    run_version(version="7", folder_path=folder_path)