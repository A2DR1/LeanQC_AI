import os

# ---------- Model configurations ----------
models = {
    "kimina_autoformalizer": {
        "model_name": "AI-MO/Kimina-Autoformalizer-7B",
        "base_url": "https://austinszj--kimina-autoformalizer-vllm-inference-serve.modal.run/v1",
        "api_key": "EMPTY",  # vLLM doesn't require a key by default
        "model_revision": "ddd47cb",
    },
    "deepseek_chat": {
        "model_name": "deepseek-chat",
        "base_url": "https://api.deepseek.com",
        "api_key": os.getenv("DEEPSEEK_API_KEY")
    },
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
You are an expert Lean 4 formalizer.

Your Task:
Translate the user's Controlled Natural Language (CNL) statement into a valid Lean 4 theorem.

Rules:
1. Use the provided imports context. Do not make up new imports.
2. Output ONLY the Lean 4 code. No explanations.
3. The theorem must end with ':= sorry' (do not attempt to prove it).
4. Use descriptive variable names.
5. Handle type coercion (e.g., Real vs Nat) carefully.
6. Do not include any imports, import context is provided.

Reference Example:
Input: "There are infinite prime numbers."
Output: 
theorem infinite_primes : ∀ n, ∃ p, n < p ∧ Nat.Prime p := sorry
"""