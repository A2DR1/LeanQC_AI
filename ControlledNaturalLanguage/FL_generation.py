import os
import sys
from pathlib import Path
import re
import json
from dotenv import load_dotenv
from openai import OpenAI
from handle_miniF2F import readFolder
from CNL_generation import read_cnl_lst
from eval_semantic import evaluate_translation
from tqdm import tqdm 
from lean_interact import LeanREPLConfig, LeanServer, Command, TempRequireProject, LeanRequire
import time

# 1. Load environment variables
load_dotenv()

# 2. Security Check
api_key = os.getenv("DEEPSEEK_API_KEY")
if not api_key:
    print("❌ Error: DEEPSEEK_API_KEY not found in .env file.")
    sys.exit(1)

# 3. Initialize Client
try:
    client = OpenAI(api_key=api_key, base_url="https://api.deepseek.com")
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
            model="deepseek-chat", # Or "deepseek-coder" if available/preferred
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

def generate_write(folder_path, name=None, json_output_path=None):
    """
    Utility to write content to a file.
    """
    print(f"📂 Processing folder/file: {folder_path}")
    t0 = time.time()

    if "miniF2F/informal" in folder_path:
        informal_statements = readFolder(folder_path)
    else:
        informal_statements = read_cnl_lst(folder_path)

    if len(informal_statements) == 0:
        print("❌ No informal statements found.")
        return 

    syntactic_corrects = []
    logs = []
    corrects = []
    reasons = []
    formal_statements = []

    project = TempRequireProject(lean_version="v4.8.0", require="mathlib")
    config = LeanREPLConfig(verbose=True, project = project)
    server = LeanServer(config)

    for statement in tqdm(informal_statements):
        # generate lean statement
        lean_statement = generate_lean(statement)
        formal_statements.append(lean_statement)

        # syntactic check
        # is_syntactic_valid, log = check_lean_code(STANDARD_IMPORTS + '\n\n' + lean_statement, checker_path)
        # is_syntactic_valid, log = lean.check(lean_statement)
        response = server.run(Command(cmd = STANDARD_IMPORTS + '\n\n' + lean_statement))
        if response.messages and response.messages[0].severity == "error":
            is_syntactic_valid = False
            log = response.messages[0].data
        elif response.messages:
            is_syntactic_valid = True
            log = response.messages[0].severity + ". " + response.messages[0].data
        else:
            is_syntactic_valid = True
            log = "No syntax errors."
        syntactic_corrects.append(is_syntactic_valid)
        logs.append(log)

        # semantic evaluation
        sem_eval = evaluate_translation(statement, lean_statement)
        err = sem_eval.get("reason", "No reason provided.")
        is_correct = sem_eval.get("is_correct", False)
        corrects.append(is_correct)
        reasons.append(err)
    

    n = len(informal_statements)

    # write into lean file 
    if name:
        with open(name, "w") as f:
            f.write(STANDARD_IMPORTS + "\n\n")
            for i in range(n):
                lean_statement = formal_statements[i]
                f.write(lean_statement + "\n\n")

    # write into json file
    if json_output_path:
        with open(json_output_path, "w") as jf:
            data = []
            for i in range(n):
                json_entry = {
                    "informal_statement": informal_statements[i],
                    "formal_statement": formal_statements[i],
                    "is_syntactically_correct": syntactic_corrects[i],
                    "syntactic_evaluation_log": logs[i],
                    "is_semantically_correct": corrects[i],
                    "semantic_evaluation_reason": reasons[i]
                }
                data.append(json_entry.copy())
            jf.write(json.dumps(data) + "\n")

    # print summary statistics
    syntax_accuracy = sum(syntactic_corrects) / len(syntactic_corrects) * 100
    print(f"\n✅ syntactic accuracy: {syntax_accuracy:.2f}% ({sum(syntactic_corrects)}/{len(syntactic_corrects)})")
    
    syntactic_correct_indices = [i for i, x in enumerate(syntactic_corrects) if x]

    if len(syntactic_correct_indices) > 0:
        corrects_filtered = [corrects[i] for i in syntactic_correct_indices]
    else:
        corrects_filtered = []
    if len(corrects_filtered) > 0:
        semantic_accuracy = sum(corrects_filtered) / len(corrects_filtered) * 100
    else:
        semantic_accuracy = 0.0
    print(f"✅ semantic accuracy: {semantic_accuracy:.2f}% ({sum(corrects_filtered)}/{len(corrects_filtered)})")

    print(f"⏱️ Total Time Spent: {time.time() - t0:.2f} seconds")

    return syntax_accuracy, semantic_accuracy

# --- Execution ---
if __name__ == "__main__":
    pass