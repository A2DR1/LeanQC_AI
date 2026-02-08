from pipeline import run_baseline_dataset, run_cnl_dataset

tasks = [
    {"FL_model": "deepseek-prover-v2", "CNL_model": "deepseek-prover-v2", "semantic_judge_model": "deepseek-prover-v2", "version": 8, "dataset": "Putnam", "limit": 100},
    {"FL_model": "deepseek-prover-v2", "CNL_model": "deepseek-prover-v2", "semantic_judge_model": "deepseek-prover-v2", "version": 8, "dataset": "miniF2F", "limit": 100},
    {"FL_model": "deepseek-prover-v2", "CNL_model": "deepseek-prover-v2", "semantic_judge_model": "deepseek-prover-v2", "version": 8, "dataset": "ProofNet", "limit": 100},
    {"FL_model": "deepseek-prover-v2", "semantic_judge_model": "deepseek-prover-v2", "dataset": "miniF2F", "limit": 100},
    {"FL_model": "kimina-autoformalizer", "CNL_model": "deepseek-prover-v2", "semantic_judge_model": "deepseek-prover-v2", "version": 8, "dataset": "Putnam", "limit": 100},
    {"FL_model": "kimina-autoformalizer", "CNL_model": "deepseek-prover-v2", "semantic_judge_model": "deepseek-prover-v2", "version": 8, "dataset": "miniF2F", "limit": 100},
    {"FL_model": "kimina-autoformalizer", "CNL_model": "deepseek-prover-v2", "semantic_judge_model": "deepseek-prover-v2", "version": 8, "dataset": "ProofNet", "limit": 100},
   
]

if __name__ == "__main__":
    print("Running Tasks Overnight...\n")

    for task in tasks:
        print("\n\n")
        print("=" * 50)
        print(f"Running task: {task}")
        try:
            if "version" in task.keys():
                tag = f"{task['dataset']}_cnl_v{task['version']}" + ("_withproof" if task.get("include_fimo_proof", False) else "")
                run_cnl_dataset(task["dataset"], task["version"], limit=task["limit"], tag=tag, include_fimo_proof=task.get("include_fimo_proof", False), FL_model=task["FL_model"], CNL_model=task["CNL_model"], semantic_judge_model=task["semantic_judge_model"])
            else:
                tag = f"{task['dataset']}_baseline" + ("_withproof" if task.get("include_fimo_proof", False) else "")
                run_baseline_dataset(task["dataset"], limit=task["limit"], tag=tag, include_fimo_proof=task.get("include_fimo_proof", False), FL_model=task["FL_model"], semantic_judge_model=task["semantic_judge_model"])
        except Exception as e:
            print(f"Error running task {task}: {e}")
            continue