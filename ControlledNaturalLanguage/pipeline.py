import json

from CNL_generation import generate_cnl, write_cnl_to_file
from FL_generation import generate_write

from read_file.handle_miniF2F import readFolder_miniF2F
from read_file.handle_putnam import readPutnam
from read_file.handle_FIMO import readFolder_fimo

CNL_PATH = "history/CNL"
LEAN_FILES_PATH = "history/Lean_files"
NL_FL_PAIRS_PATH = "history/NL_FL_pairs"

MINIF2F_FOLDER = "testbench/miniF2F/test"
FIMO_FOLDER = "testbench/FIMO"


# -----------------------------
# Utilities
# -----------------------------
def prompt_choice(prompt: str, valid: set[str]) -> str:
    while True:
        choice = input(prompt).strip().lower()
        if choice in valid:
            return choice
        print(f"❌ Invalid input. Expected one of: {sorted(valid)}")


def prompt_int(prompt: str, valid_range=None) -> int:
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


def ask_include_fimo_proof() -> bool:
    ans = prompt_choice(
        prompt="\nInclude FIMO informal proof? (y/n)\n> ",
        valid={"y", "n"},
    )
    return ans == "y"


def load_cnl_rules(version: int) -> tuple[str, str | None, str | None]:
    with open("cnl_rules.json", "r", encoding="utf-8") as f:
        pack = json.load(f).get(f"v{version}")
    if pack is None:
        raise ValueError(f"CNL rules for v{version} not found in cnl_rules.json")

    cnl_rules = pack["rules"]
    input_example = pack.get("example_input")
    output_example = pack.get("example_output")
    return cnl_rules, input_example, output_example


def read_dataset_statements(dataset_name: str, limit: int, randomize: bool, include_fimo_proof: bool) -> list[str]:
    if dataset_name == "miniF2F":
        return readFolder_miniF2F(MINIF2F_FOLDER, limit=limit, randomize=randomize)

    if dataset_name == "putnam":
        return readPutnam(limit=limit, randomize=randomize, include_solution=True)

    if dataset_name == "fimo":
        return readFolder_fimo(
            folder_path=FIMO_FOLDER,
            limit=limit,
            randomize=randomize,
            include_proof=include_fimo_proof,
        )

    raise ValueError(f"Unknown dataset: {dataset_name}")


# -----------------------------
# Baseline and CNL runners
# -----------------------------
def run_baseline_dataset(dataset_name: str, limit=100, randomize=False, tag="baseline", include_fimo_proof=False):
    raw_statements = read_dataset_statements(
        dataset_name=dataset_name,
        limit=limit,
        randomize=randomize,
        include_fimo_proof=include_fimo_proof,
    )

    raw_json_path = f"{CNL_PATH}/raw_statements_{tag}.json"
    write_cnl_to_file(raw_statements, filename=raw_json_path)

    generate_write(
        raw_json_path,
        name=f"{LEAN_FILES_PATH}/Autoformalized_{tag}.lean",
        json_output_path=f"{NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json",
    )

    print(f"\n✅ Saved raw statements to {raw_json_path}")
    print(f"✅ Saved Lean output to {LEAN_FILES_PATH}/Autoformalized_{tag}.lean")
    print(f"✅ Saved NL-FL pairs to {NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json")


def run_cnl_dataset(dataset_name: str, version: int, limit=100, tag=None, include_fimo_proof=False):
    if tag is None:
        tag = f"{dataset_name}_cnl_v{version}"

    base_statements = read_dataset_statements(
        dataset_name=dataset_name,
        limit=limit,
        randomize=True,
        include_fimo_proof=include_fimo_proof,
    )

    cnl_rules, input_example, output_example = load_cnl_rules(version)

    cnl_statements = [
        generate_cnl(s, cnl_rules=cnl_rules, input_example=input_example, output_example=output_example)
        for s in base_statements
    ]

    cnl_json_path = f"{CNL_PATH}/cnl_statements_{tag}.json"
    write_cnl_to_file(cnl_statements, filename=cnl_json_path)

    generate_write(
        cnl_json_path,
        name=f"{LEAN_FILES_PATH}/Autoformalized_{tag}.lean",
        json_output_path=f"{NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json",
    )

    print(f"\n✅ Saved CNL statements to {cnl_json_path}")
    print(f"✅ Saved CNL autoformalizations to {LEAN_FILES_PATH}/Autoformalized_{tag}.lean")
    print(f"✅ Saved NL-FL pairs to {NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json")


# -----------------------------
# Scoring (kept compatible with your existing JSON format)
# -----------------------------
def count_corrects(file_path: str):
    with open(file_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    syntactic_corrects = [entry["is_syntactically_correct"] for entry in data]
    semantic_corrects = [entry["is_semantically_correct"] for entry in data if entry["is_syntactically_correct"]]

    syntax_accuracy = (sum(syntactic_corrects) / len(syntactic_corrects) * 100) if syntactic_corrects else 0.0
    semantic_accuracy = (sum(semantic_corrects) / len(semantic_corrects) * 100) if semantic_corrects else 0.0

    print(f"Syntactic Correct: {sum(syntactic_corrects)}/{len(syntactic_corrects)}")
    print(f"Semantic Correct:  {sum(semantic_corrects)}/{len(semantic_corrects)}")
    print(f"\n✅ Syntactic Accuracy: {syntax_accuracy:.2f}%")
    print(f"✅ Semantic Accuracy:  {semantic_accuracy:.2f}%")


def overall_accuracy(file_path: str) -> float:
    with open(file_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    semantic_corrects = [entry["is_semantically_correct"] for entry in data if entry["is_syntactically_correct"]]
    overall = (sum(semantic_corrects) / len(data) * 100) if data else 0.0

    print(f"✅ Overall Accuracy:  {overall:.2f}%")
    return overall


# -----------------------------
# Main
# -----------------------------
if __name__ == "__main__":
    dataset_sel = prompt_int(
        prompt=(
            "\nSelect dataset:\n"
            "  1) MiniF2F\n"
            "  2) Putnam\n"
            "  3) FIMO\n"
            "> "
        ),
        valid_range={1, 2, 3},
    )
    dataset_name = {1: "miniF2F", 2: "putnam", 3: "fimo"}[dataset_sel]

    include_fimo_proof = False
    if dataset_name == "fimo":
        include_fimo_proof = ask_include_fimo_proof()

    run_mode = prompt_choice(
        prompt="\nRun mode:\n  b) baseline (raw NL)\n  c) CNL version\n> ",
        valid={"b", "c"},
    )

    if run_mode == "b":
        tag = f"{dataset_name}_baseline" + ("_withproof" if include_fimo_proof else "")
        run_baseline_dataset(dataset_name, limit=100, randomize=True, tag=tag, include_fimo_proof=include_fimo_proof)
    else:
        version_sel = prompt_int("\nWhich CNL version? (1-7)\n> ", valid_range=set(range(1, 8)))
        tag = f"{dataset_name}_cnl_v{version_sel}" + ("_withproof" if include_fimo_proof else "")
        run_cnl_dataset(dataset_name, version_sel, limit=100, tag=tag, include_fimo_proof=include_fimo_proof)

    output_json = f"{NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json"
    print(f"\n📌 Scoring file: {output_json}\n")
    count_corrects(output_json)
    overall_accuracy(output_json)