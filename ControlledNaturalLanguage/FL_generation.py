import os
import sys
from pathlib import Path
import re
import json
from dotenv import load_dotenv
from openai import OpenAI
from read_file.handle_miniF2F import readFolder_miniF2F
from CNL_generation import read_cnl_lst
from eval_semantic import evaluate_translation
from tqdm import tqdm 
from lean_interact import LeanREPLConfig, LeanServer, Command, TempRequireProject, LeanRequire
import time

from config import models

# 1. Load environment variables
load_dotenv()

model_name = "kimina_autoformalizer"
model = models.get(model_name, {})
if not model:
    print(f"❌ Error: '{model_name}' config not found in config.py.")
    sys.exit(1)

# 2. Security Check
api_key = model.get("api_key", "")
if not api_key:
    print(f"❌ Error: API key for '{model_name}' not found in config.py.")
    sys.exit(1)

# 3. Initialize Client
try:
    client = OpenAI(api_key=api_key, base_url=model.get("base_url", ""))
except Exception as e:
    print(f"❌ Error initializing client: {e}")
    sys.exit(1)

# --- Configuration ---

# The "Oracle Context": Standard imports to help the model find definitions.
# In a full system, you would retrieve these dynamically. For PoC, this covers 90% of undergrad math.
STANDARD_IMPORTS = """
import Mathlib
set_option maxHeartbeats 0
set_option autoImplicit false
set_option pp.numericTypes true
set_option pp.coercions true
set_option pp.letVarTypes true
set_option pp.structureInstanceTypes true
set_option pp.instanceTypes true
set_option pp.mvars.withType true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
open scoped BigOperators
open Real Nat Topology Rat Filter Finset Set
"""

def clean_lean_output(raw_text):
    """
    Cleans the LLM output to return *only* the code.
    Removes markdown backticks (```lean ... ```) and conversational filler.
    """
    # Remove markdown code blocks
    clean = re.sub(r"```lean\n", "", raw_text)
    clean = re.sub(r"```", "", clean)
    
    # If the model adds "Here is the code:", try to split and take the last part
    # (This is a heuristic, usually the code block handles it)
    return clean.strip()

def generate_lean(cnl_statement, imports=STANDARD_IMPORTS):
    """
    Autoformalizes a CNL/NL statement into a Lean 4 Theorem.
    """
    # print(f"🤖 Autoformalizing: '{cnl_statement[:50]}...'")

    system_prompt = f"""
    You are an expert Lean 4 formalizer.
    
    Your Task:
    Translate the user's Controlled Natural Language (CNL) statement into a valid Lean 4 theorem.
    
    Rules:
    1. Use the provided imports context. Do not make up new imports.
    2. Output ONLY the Lean 4 code. No explanations.
    3. The theorem must end with ':= sorry' (do not attempt to prove it).
    4. Use descriptive variable names.
    5. Handle type coercion (e.g., Real vs Nat) carefully.

    Reference Example:
    Input: "There are infinite prime numbers."
    Output: 
    theorem infinite_primes : ∀ n, ∃ p, n < p ∧ Nat.Prime p := sorry
    """

    user_prompt = f"""
    Context (Imports):
    {imports}

    Statement to Formalize:
    {cnl_statement}
    """

    try:
        response = client.chat.completions.create(
            model=model.get("model_name", ""),
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
            temperature=0.2, # Low temp for syntax precision
            stream=False
        )
        
        raw_output = response.choices[0].message.content
        return clean_lean_output(raw_output)

    except Exception as e:
        return f"❌ API Error: {e}"

def generate_write(input_path, name=None, json_output_path=None):
    """
    Generate Lean formalizations for a list of statements.

    input_path can be:
      - a directory of miniF2F json files (readFolder_miniF2F)
      - a json file containing List[str] (read_cnl_lst)
    """
    print(f"📂 Processing: {input_path}")
    t0 = time.time()

    # ---------- Load statements ----------
    if os.path.isdir(input_path):
        # treat as dataset folder
        informal_statements = readFolder_miniF2F(input_path, limit=100)
    else:
        # treat as json file containing List[str]
        informal_statements = read_cnl_lst(input_path)

    if not informal_statements:
        print("❌ No statements found.")
        return

    syntactic_corrects: list[bool] = []
    logs: list[str] = []
    semantic_corrects: list[bool] = []
    reasons: list[str] = []
    formal_statements: list[str] = []

    project = TempRequireProject(lean_version="v4.8.0", require="mathlib")
    config = LeanREPLConfig(verbose=False, project=project)
    server = LeanServer(config)

    try:
        for statement in tqdm(informal_statements):
            lean_statement = generate_lean(statement)
            formal_statements.append(lean_statement)

            # --- Syntactic check ---
            resp = server.run(Command(cmd=STANDARD_IMPORTS + "\n\n" + lean_statement))

            # If ANY error message exists → fail
            error_msgs = [m for m in (resp.messages or []) if getattr(m, "severity", "") == "error"]
            if error_msgs:
                is_syntactic_valid = False
                # join all error messages for debugging
                log = "\n".join([getattr(m, "data", str(m)) for m in error_msgs])
            else:
                is_syntactic_valid = True
                # include warnings if present
                if resp.messages:
                    log = "\n".join([f"{m.severity}: {m.data}" for m in resp.messages])
                else:
                    log = "No messages."

            syntactic_corrects.append(is_syntactic_valid)
            logs.append(log)

            # --- Semantic evaluation (only if syntactically valid) ---
            if is_syntactic_valid:
                sem_eval = evaluate_translation(statement, lean_statement)
                is_correct = bool(sem_eval.get("is_correct", False))
                reason = sem_eval.get("reason", "No reason provided.")
            else:
                is_correct = False
                reason = "Skipped semantic eval because syntactic check failed."

            semantic_corrects.append(is_correct)
            reasons.append(reason)

    finally:
        # important: cleanup
        try:
            server.close()
        except Exception:
            pass
        try:
            project.close()
        except Exception:
            pass

    n = len(informal_statements)

    # ---------- Write Lean file ----------
    if name:
        with open(name, "w", encoding="utf-8") as f:
            f.write(STANDARD_IMPORTS.strip() + "\n\n")
            for st in formal_statements:
                f.write(st.strip() + "\n\n")

    # ---------- Write JSON file ----------
    if json_output_path:
        data = []
        for i in range(n):
            data.append({
                "informal_statement": informal_statements[i],
                "formal_statement": formal_statements[i],
                "is_syntactically_correct": syntactic_corrects[i],
                "syntactic_evaluation_log": logs[i],
                "is_semantically_correct": semantic_corrects[i],
                "semantic_evaluation_reason": reasons[i],
            })

        with open(json_output_path, "w", encoding="utf-8") as jf:
            json.dump(data, jf, indent=2, ensure_ascii=False)

    # ---------- Summary ----------
    syntax_accuracy = (sum(syntactic_corrects) / n) * 100 if n else 0.0

    syntactic_pass_idxs = [i for i, ok in enumerate(syntactic_corrects) if ok]
    semantic_filtered = [semantic_corrects[i] for i in syntactic_pass_idxs]
    semantic_accuracy = (sum(semantic_filtered) / len(semantic_filtered)) * 100 if semantic_filtered else 0.0

    print(f"\n✅ syntactic accuracy: {syntax_accuracy:.2f}% ({sum(syntactic_corrects)}/{n})")
    print(f"✅ semantic accuracy:  {semantic_accuracy:.2f}% ({sum(semantic_filtered)}/{len(semantic_filtered)})")
    print(f"⏱️ Total Time Spent: {time.time() - t0:.2f} seconds")

    return syntax_accuracy, semantic_accuracy

# --- Execution ---
if __name__ == "__main__":
    pass