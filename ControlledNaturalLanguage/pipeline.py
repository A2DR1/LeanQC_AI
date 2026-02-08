import json
from tqdm import tqdm

from CNL_generation import CNL_generator
from FL_generation import FL_generator
from Quality_reducer import qualityReducer

CNL_PATH = "history/CNL"
LEAN_FILES_PATH = "history/Lean_files"
NL_FL_PAIRS_PATH = "history/NL_FL_pairs"

MINIF2F_FOLDER = "testbench/miniF2F/test"
PUTNAM_FOLDER = "testbench/Putnam/putnam.json"
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
    input_example = pack.get("example_input", None)
    output_example = pack.get("example_output", None)
    return cnl_rules, input_example, output_example


def read_dataset_statements(dataset_name: str, limit: int, randomize: bool, include_fimo_proof: bool) -> list[str]:
    if dataset_name == "miniF2F":
        from read_file.handle_miniF2F import miniF2FHandler
        handler = miniF2FHandler()
        return handler.read(MINIF2F_FOLDER, limit=limit, randomize=randomize)

    if dataset_name == "Putnam":
        from read_file.handle_Putnam import PutnamHandler
        handler = PutnamHandler()
        return handler.read(limit=limit, randomize=randomize, include_solution=True)

    if dataset_name == "FIMO":
        from read_file.handle_FIMO import FIMOHandler
        handler = FIMOHandler()
        return handler.read(
            folder_path=FIMO_FOLDER,
            limit=limit,
            randomize=randomize,
            include_proof=include_fimo_proof,
        )
    
    if dataset_name == "ProofNet":
        from read_file.handle_ProofNet import ProofNetHandler
        handler = ProofNetHandler()
        return handler.read(limit=limit, randomize=randomize)

    raise ValueError(f"Unknown dataset: {dataset_name}")


# -----------------------------
# Baseline and CNL runners
# -----------------------------
def run_baseline_dataset(dataset_name: str, limit=100, randomize=False, tag="baseline", include_fimo_proof=False, FL_model="kimina_autoformalizer", sematnic_judge_model="deepseek-R1", apply_quality_reduction=False):
    raw_statements = read_dataset_statements(
        dataset_name=dataset_name,
        limit=limit,
        randomize=randomize,
        include_fimo_proof=include_fimo_proof,
    )

    original_statements = raw_statements.copy()  # Keep a copy of original statements for reference

    if apply_quality_reduction:
        print("Applying quality reduction to statements...")
        reducer = qualityReducer(model_name="deepseek-chat")
        raw_statements = [
            reducer.reduce_quality(s) or s  # If reduction fails, keep original
            for s in tqdm(raw_statements, desc="Reducing Quality", unit="statement")
        ]

    raw_json_path = f"{CNL_PATH}/raw_statements_{tag}.json"
    fl_generator = FL_generator(isCNL=True, model_name=FL_model)
    cnl_generator = CNL_generator() # just for writing raw statements to json, not actually generating CNL
    cnl_generator.write_cnl_to_file(raw_statements, filename=raw_json_path)

    fl_generator.generate_write(
        raw_json_path,
        name=f"{LEAN_FILES_PATH}/Autoformalized_{tag}.lean",
        json_output_path=f"{NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json",
        semantic_judge_model=sematnic_judge_model,
    )

    print(f"\n✅ Saved raw statements to {raw_json_path}")
    print(f"✅ Saved Lean output to {LEAN_FILES_PATH}/Autoformalized_{tag}.lean")
    print(f"✅ Saved NL-FL pairs to {NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json")


def run_cnl_dataset(dataset_name: str, version: int, limit=100, tag=None, include_fimo_proof=False, FL_model="kimina_autoformalizer", CNL_model="deepseek-R1", semantic_judge_model="deepseek-R1", apply_quality_reduction=False):
    if tag is None:
        tag = f"{dataset_name}_cnl_v{version}"

    base_statements = read_dataset_statements(
        dataset_name=dataset_name,
        limit=limit,
        randomize=True,
        include_fimo_proof=include_fimo_proof,
    )

    original_statements = base_statements.copy()  # Keep a copy of original statements for reference

    if apply_quality_reduction:
        print("Applying quality reduction to statements...")
        reducer = qualityReducer(model_name="deepseek-chat")
        base_statements = [
            reducer.reduce_quality(s) or s  # If reduction fails, keep original
            for s in tqdm(base_statements, desc="Reducing Quality", unit="statement")
        ]

    print("Generating CNL statements...")
    cnl_rules, input_example, output_example = load_cnl_rules(version)
    cnl_generator = CNL_generator(benchmark_name=dataset_name, cnl_rules_path="cnl_rules.json", model_name=CNL_model)
    cnl_statements = [
        cnl_generator.generate_cnl(s, cnl_rules=cnl_rules, input_example=input_example, output_example=output_example)
        for s in tqdm(base_statements, desc="Generating CNL", unit="statement")
    ]

    cnl_json_path = f"{CNL_PATH}/cnl_statements_{tag}.json"
    cnl_generator.write_cnl_to_file(cnl_statements, filename=cnl_json_path)

    fl_generator = FL_generator(dataset_name=dataset_name, isCNL=True, model_name=FL_model)
    fl_generator.generate_write(
        cnl_json_path,
        name=f"{LEAN_FILES_PATH}/Autoformalized_{tag}.lean",
        json_output_path=f"{NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json",
        CNL_model=CNL_model,
        semantic_judge_model=semantic_judge_model,
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

    FL_model_sel = prompt_choice(
        prompt=(
            "\nSelect model for FL generation:\n"
            "  1) kimina_autoformalizer (smaller, faster, open weights)\n"
            "  2) deepseek-chat (stronger external judge, but slower and costs money)\n"
            "  3) herald_autoformalizer\n"
            "  4) deepseek-R1 (stronger than deepseek-chat, but slower and costs more)\n"
            "  5) deepseek-prover-v2 (strongest, but slowest and most expensive)\n"
            "> "
        ),
        valid={"1", "2", "3", "4", "5"},
    )
    FL_model_name = {"1": "kimina_autoformalizer", "2": "deepseek-chat", "3": "herald_autoformalizer", "4": "deepseek-R1", "5": "deepseek-prover-v2"}[FL_model_sel]

    Semantic_judge_sel = prompt_choice(
        prompt=(
            "\nSelect model for semantic evaluation:\n"
            "  1) deepseek-chat (stronger external judge, but slower and costs money)\n"
            "  2) deepseek-R1 (stronger than deepseek-chat, but slower and costs more)\n"
            "  3) deepseek-prover-v2 (strongest, but slowest and most expensive)\n"
            "> "
        ),
        valid={"1", "2", "3"},
    )
    Semantic_judge_model_name = {"1": "deepseek-chat", "2": "deepseek-R1", "3": "deepseek-prover-v2"}[Semantic_judge_sel]

    dataset_sel = prompt_int(
        prompt=(
            "\nSelect dataset:\n"
            "  1) miniF2F\n"
            "  2) Putnam\n"
            "  3) FIMO\n"
            "  4) ProofNet\n"
            "> "
        ),
        valid_range={1, 2, 3, 4},
    )
    dataset_name = {1: "miniF2F", 2: "Putnam", 3: "FIMO", 4: "ProofNet"}[dataset_sel]

    include_fimo_proof = False
    if dataset_name == "FIMO":
        include_fimo_proof = ask_include_fimo_proof()

    run_mode = prompt_choice(
        prompt="\nRun mode:\n  b) baseline (raw NL)\n  c) CNL version\n> ",
        valid={"b", "c"},
    )

    isQuality_reduce = prompt_choice(
        prompt="\nApply quality reduction to FL outputs? (y/n)\n> ",
        valid={"y", "n"},
    )
    apply_quality_reduction = isQuality_reduce == "y"

    limit = prompt_int("\nHow many problems to process? (e.g., 100)\n> ", valid_range=set(range(1, 1001)))

    if run_mode == "b":
        tag = f"{dataset_name}_baseline" + ("_withproof" if include_fimo_proof else "")
        run_baseline_dataset(dataset_name, limit=limit, randomize=False, tag=tag, include_fimo_proof=include_fimo_proof, FL_model=FL_model_name, sematnic_judge_model=Semantic_judge_model_name, apply_quality_reduction=apply_quality_reduction)
    else:

        CNL_Model_sel = prompt_choice(
            prompt=(
                "\nSelect model for CNL generation:\n"
                "  1) kimina_autoformalizer (smaller, faster, open weights)\n"
                "  2) deepseek-chat (stronger external judge, but slower and costs money)\n"
                "  3) herald_autoformalizer\n"
                "  4) deepseek-R1 (stronger than deepseek-chat, but slower and costs more)\n"
                "  5) deepseek-prover-v2 (strongest, but slowest and most expensive)\n"
                "> "
            ),
            valid={"1", "2", "3", "4", "5"},
        )
        CNL_model_name = {"1": "kimina_autoformalizer", "2": "deepseek-chat", "3": "herald_autoformalizer", "4": "deepseek-R1", "5": "deepseek-prover-v2"}[CNL_Model_sel]

        version_sel = prompt_int("\nWhich CNL version? (1-9)\n> ", valid_range=set(range(1, 10)))
        tag = f"{dataset_name}_cnl_v{version_sel}" + ("_withproof" if include_fimo_proof else "")
        run_cnl_dataset(dataset_name, version_sel, limit=limit, tag=tag, include_fimo_proof=include_fimo_proof, FL_model=FL_model_name, CNL_model=CNL_model_name, semantic_judge_model=Semantic_judge_model_name, apply_quality_reduction=apply_quality_reduction)

    output_json = f"{NL_FL_PAIRS_PATH}/NL_FL_pairs_{tag}.json"
    print(f"\n📌 Scoring file: {output_json}\n")
    count_corrects(output_json)
    overall_accuracy(output_json)