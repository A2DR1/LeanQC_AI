from CNL_generation import generate_cnl_list, read_cnl_lst, write_cnl_to_file
from FL_generation import generate_write
from read_file.handle_miniF2F import readFolder_miniF2F
from read_file.handle_putnam import readPutnam


CNL_path = 'history/CNL'
Lean_files_path = 'history/Lean_files'
NL_FL_pairs_path = 'history/NL_FL_pairs'
folder_path = "testbench/miniF2F/test"

def run_baseline_dataset(dataset_name: str, limit=100, randomize=False, tag="baseline"):
    if dataset_name == "miniF2F":
        raw_statements = readFolder_miniF2F(folder_path, limit=limit, randomize=randomize)
    elif dataset_name == "putnam":
        raw_statements = readPutnam(limit=limit, randomize=randomize, include_solution=True)
    else:
        raise ValueError(f"Unknown dataset: {dataset_name}")

    raw_json_path = f"{CNL_path}/raw_statements_{tag}.json"
    write_cnl_to_file(raw_statements, filename=raw_json_path)

    generate_write(
        raw_json_path,
        name=f"{Lean_files_path}/Autoformalized_{tag}.lean",
        json_output_path=f"{NL_FL_pairs_path}/NL_FL_pairs_{tag}.json"
    )

    print(f"\n✅ Saved raw statements to {raw_json_path}")
    print(f"✅ Saved Lean output to {Lean_files_path}/Autoformalized_{tag}.lean")
    print(f"✅ Saved NL-FL pairs to {NL_FL_pairs_path}/NL_FL_pairs_{tag}.json")

def run_cnl_dataset(dataset_name: str, version: int, limit=100, tag=None):
    if tag is None:
        tag = f"{dataset_name}_cnl_v{version}"

    # 1) get base NL statements per dataset
    if dataset_name == "miniF2F":
        base_statements = readFolder_miniF2F(folder_path, limit=limit, randomize=True)
    elif dataset_name == "putnam":
        base_statements = readPutnam(limit=limit, randomize=True, include_solution=True)
    else:
        raise ValueError(f"Unknown dataset: {dataset_name}")

    # 2) CNL rewrite each statement using your existing generate_cnl(...)
    #    (this avoids generate_cnl_list being tied to miniF2F folder_path)
    from CNL_generation import generate_cnl  # reuse your function
    import json

    with open("cnl_rules.json", "r") as f:
        rules_pack = json.load(f).get(f"v{version}")
        if rules_pack is None:
            raise ValueError(f"CNL rules for v{version} not found in cnl_rules.json")
        cnl_rules = rules_pack["rules"]
        input_example = rules_pack.get("example_input")
        output_example = rules_pack.get("example_output")

    cnl_statements = [
        generate_cnl(s, cnl_rules=cnl_rules, input_example=input_example, output_example=output_example)
        for s in base_statements
    ]

    cnl_json_path = f"{CNL_path}/cnl_statements_{tag}.json"
    write_cnl_to_file(cnl_statements, filename=cnl_json_path)

    generate_write(
        cnl_json_path,
        name=f"{Lean_files_path}/Autoformalized_{tag}.lean",
        json_output_path=f"{NL_FL_pairs_path}/NL_FL_pairs_{tag}.json"
    )

    print(f"\n✅ Saved CNL statements to {cnl_json_path}")
    print(f"✅ Saved CNL autoformalizations to {Lean_files_path}/Autoformalized_{tag}.lean")
    print(f"✅ Saved NL-FL pairs to {NL_FL_pairs_path}/NL_FL_pairs_{tag}.json")

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

def prompt_choice(prompt: str, valid: set[str]) -> str:
    """Prompt until user enters a valid choice."""
    while True:
        choice = input(prompt).strip().lower()
        if choice in valid:
            return choice
        print(f"❌ Invalid input. Expected one of: {sorted(valid)}")


def prompt_int(prompt: str, valid_range=None) -> int:
    """Prompt for an integer; optionally enforce a range/set."""
    while True:
        raw = input(prompt).strip()
        try:
            value = int(raw)
        except ValueError:
            print("❌ Please enter an integer.")
            continue

        if valid_range is not None and value not in valid_range:
            print(f"❌ Invalid choice. Expected one of: {sorted(valid_range)}")
            continue
        return value


if __name__ == "__main__":

    dataset_sel = prompt_int(
        prompt=(
            "\nSelect dataset:\n"
            "  1) MiniF2F\n"
            "  2) Putnam\n"
            "> "
        ),
        valid_range={1, 2}
    )
    dataset_name = "miniF2F" if dataset_sel == 1 else "putnam"

    run_mode = prompt_choice(
        prompt="\nRun mode:\n  b) baseline (raw NL)\n  c) CNL version\n> ",
        valid={"b", "c"}
    )

    if run_mode == "b":
        tag = f"{dataset_name}_baseline"
        run_baseline_dataset(dataset_name, limit=100, randomize=True, tag=tag)
    else:
        version_sel = prompt_int(
            prompt="\nWhich CNL version? (1-7)\n> ",
            valid_range=set(range(1, 8))
        )
        tag = f"{dataset_name}_cnl_v{version_sel}"
        run_cnl_dataset(dataset_name, version_sel, limit=100, tag=tag)

    output_json = f"{NL_FL_pairs_path}/NL_FL_pairs_{tag}.json"
    print(f"\n📌 Scoring file: {output_json}\n")
    count_corrects(file_path=output_json)
    overall_accuracy(file_path=output_json)
