import os
from dotenv import load_dotenv
load_dotenv()

# ---------- Model configurations ----------
models = {
    "kimina_autoformalizer": {
        "model_name": "AI-MO/Kimina-Autoformalizer-7B",
        "base_url": "https://austinszj--kimina-autoformalizer-vllm-inference-serve.modal.run/v1",
        "api_key": "EMPTY",  # vLLM doesn't require a key by default
        "model_revision": "ddd47cb",
    },
    "deepseek-chat": {
        "model_name": "deepseek-chat",
        "base_url": "https://api.deepseek.com",
        "api_key": os.getenv("DEEPSEEK_API_KEY")
    },
    "herald_autoformalizer": {
        "model_name": "FrenzyMath/Herald_translator",
        "base_url": "https://austinszj--herald-autoformalizer-vllm-inference-serve.modal.run/v1",
        "api_key": "EMPTY",  # vLLM doesn't require a key by default
        "model_revision": "c819f87",
    },
    "deepseek-R1": {
        "model_name": "fireworks/deepseek-r1-0528",
        "base_url": "https://api.fireworks.ai/inference/v1",
        "api_key": os.getenv("FIREWORK_API_KEY"),
    },
    "deepseek-prover-v2": {
        "model_name": "deepseek-ai/DeepSeek-Prover-V2-671B:novita",
        "base_url": "https://router.huggingface.co/v1",
        "api_key": os.getenv("HF_TOKEN"),
    }
}

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

SYSTEM_PROMPT = """
You are an expert Lean 4 formalizer. Your goal is to convert Controlled Natural Language (CNL) into rigorous Lean 4 code.

Your Task:
Translate the user's CNL statement into a valid Lean 4 theorem.

Strict Constraints:
1. CODE ONLY: Output ONLY the Lean 4 code. No explanations, no markdown code blocks, no prose.
2. SYNTAX: End the theorem with ':= sorry'.
3. NO IMPORTS: Do not include import statements.
4. NAMESPACING: Use fully qualified names (e.g., 'Nat.Prime') to avoid ambiguity.
5. THE "LET" RULE (SCOPING): 
   - Do not translate "Let x be..." as a 'let' statement inside the theorem body. 
   - Instead, translate "Let" statements as universal binders (∀) or as explicit antecedents in the implication (e.g., 'n > 0 → ...'). 
   - 'let' should only be used for internal local definitions to simplify complex expressions, never for declaring the primary objects of study.
6. TYPE COERCION: Explicitly handle casts between types (e.g., using '↑').
7. BINDING: Ensure all variables are bound. Use (n : ℕ) or ∀ n, rather than assuming free variables.

Refined Example:
Input: "Let G be a group. Let H be a subgroup of G. If x is in H, then x is in G."
Output:
theorem element_in_subgroup_in_group {G : Type*} [Group G] (H : Subgroup G) (x : G) (hx : x ∈ H) : x ∈ G := sorry
"""

DEGRADER_PROMPT = """
You are an "Adversarial Math Rewriter." Your goal is to take a clear, formal mathematical statement and rewrite it into "Low Quality" informal English, mimicking a lazy student or a hastily written forum post.

Original Statement: "{clean_statement}"

Apply a combination of the following degradation rules:
1. **Type Erasure:** Change "positive integer n" to "number n" or just "n".
2. **Implicit Quantifiers:** Change "For all x" to "Whenever x..." or just "x satisfies...".
3. **Imprecise Verbs:** Change "converges to" to "goes to" or "approaches". Change "divides" to "goes into".
4. **Formatting Laziness:** Remove some LaTeX delimiters ($). Write formulas in plain text (e.g., "x^2" instead of "$x^2$").
5. **Narrative Fluff:** Add conversational filler like "Suppose we have..." or "Show that it works."
6. **Variable Swapping (Optional):** Occasionally use non-standard variables (e.g., use 'f' for a number instead of a function).

**Constraint:** The mathematical *meaning* must remain preserved (a human mathematician should still understand it), but it should be difficult for a strict parser to handle.

Output ONLY the degraded statement.
"""