from CNL_generation import generate_cnl_list, read_cnl_lst, write_cnl_to_file
from FL_generation import generate_write
from read_file.handle_miniF2F import readFolder


CNL_path = 'history/CNL'
Lean_files_path = 'history/Lean_files'
NL_FL_pairs_path = 'history/NL_FL_pairs'
folder_path = "testbench/miniF2F/test"

def run_baseline(limit=100, randomize=False, tag="baseline"):
    # 1. read raw informal statements, no CNL rewrite
    raw_statements = readFolder(folder_path, limit=limit, randomize=randomize)

    # 2. save it in json format
    raw_json_path = f"{CNL_path}/raw_statements_{tag}.json"
    write_cnl_to_file(raw_statements, filename=raw_json_path)

    # 3. autoformalization
    generate_write(
        raw_json_path,
        name=f"{Lean_files_path}/Autoformalized_{tag}.lean",
        json_output_path=f"{NL_FL_pairs_path}/NL_FL_pairs_{tag}.json"
    )

    print(f"\n✅ Saved raw statements to {raw_json_path}")
    print(f"✅ Saved Lean output to {Lean_files_path}/Autoformalized_{tag}.lean")
    print(f"✅ Saved NL-FL pairs to {NL_FL_pairs_path}/NL_FL_pairs_{tag}.json")

def run_version(version = None):
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
    run_baseline(limit=100, randomize=True, tag="baseline")
    count_corrects(file_path=f"{NL_FL_pairs_path}/NL_FL_pairs_baseline.json")
    overall_accuracy(file_path=f"{NL_FL_pairs_path}/NL_FL_pairs_baseline.json")
    # run_version(0)
    # count_corrects()
    # overall_accuracy()