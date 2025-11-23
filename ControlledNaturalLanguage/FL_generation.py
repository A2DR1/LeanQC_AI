import os
import sys
import re
from dotenv import load_dotenv
from openai import OpenAI

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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open BigOperators Real Nat Topology Rat
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
    print(f"🤖 Autoformalizing: '{cnl_statement[:50]}...'")

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

# --- Execution ---
if __name__ == "__main__":
    # Example 1: Simple Number Theory
    print("\n--- Test Case 1: Simple ---")
    cnl_1 = "Show that for every natural number n, there exists a prime number p greater than n."
    lean_1 = generate_lean(cnl_1)
    print(f"result:\n{lean_1}")

    # Example 2: Your Logarithm Problem (From CNL_generation.py)
    print("\n--- Test Case 2: Complex (Logarithms) ---")
    cnl_2 = (
        "Let x, y, and z be real numbers greater than 1. "
        "Let w be a positive real number. "
        "Assume log_x(w) = 24. "
        "Assume log_y(w) = 40. "
        "Assume log_(xyz)(w) = 12. "
        "Show that log_z(w) = 60."
    )
    lean_2 = generate_lean(cnl_2)
    print(f"result:\n{lean_2}")
    
    # Optional: Save to file for the compiler check later
    with open("Autoformalized_Theorems.lean", "w") as f:
        f.write(STANDARD_IMPORTS + "\n\n")
        f.write(lean_1 + "\n\n")
        f.write(lean_2 + "\n")
    print("\n✅ Saved results to Autoformalized_Theorems.lean")