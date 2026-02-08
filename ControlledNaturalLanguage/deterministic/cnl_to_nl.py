import json
from jinja2 import Template

# ==========================================
# 1. THE STRICT TEMPLATE (The "Compiler")
# ==========================================
# This template enforces the v9 structure:
# - NO `let` bindings in the signature.
# - ALL definitions are lifted to parameters + equality hypotheses.
# - Standard Mathlib imports are pre-loaded.
# ==========================================

LEAN_TEMPLATE_STR = """
import Mathlib

open Real Nat Set Finset Function Polynomial

{% if raw_lean_override %}
-- ESCAPE HATCH USED: Raw Lean Code Injected
{{ raw_lean_override }}
{% else %}
theorem {{ problem_name }}
  -- 1. Parameters (Universal Quantifiers)
  {%- for param in parameters %}
  ({{ param.id }} : {{ param.type }})
  {%- for constr in param.constraints %}
  (h_{{ param.id }}_{{ loop.index }} : {{ constr }})
  {%- endfor %}
  {%- endfor %}

  -- 2. Definitions (Lifted to Hypotheses)
  -- We transform "Let S = ..." into "(S : Set Nat) (h_S : S = ...)"
  {%- for def in definitions %}
  ({{ def.id }} : {{ def.type }})
  (h_def_{{ def.id }} : {{ def.id }} = {{ def.value }})
  {%- endfor %}

  : 
  -- 3. The Goal
  {{ goal }} := by
  sorry
{% endif %}
"""

class LeanTranslator:
    def __init__(self):
        self.template = Template(LEAN_TEMPLATE_STR)

    def render(self, cnl_json):
        """
        Converts CNL JSON structure into a valid Lean 4 theorem.
        """
        # strict_render ensures if variables are missing it raises an error
        return self.template.render(cnl_json)

# ==========================================
# 2. TEST DATA (Simulating DeepSeek-R1 Output)
# ==========================================

# CASE A: A Standard Problem (MiniF2F Style)
# Problem: "Let n be a positive integer. Let S be the sum of integers from 1 to n. Prove S = n(n+1)/2."
standard_problem = {
    "problem_name": "sum_of_integers",
    "raw_lean_override": None,  # Standard mode
    "parameters": [
        {"id": "n", "type": "ℕ", "constraints": ["n > 0"]}
    ],
    "definitions": [
        # Note: We define S as a parameter equal to the sum
        {"id": "S", "type": "ℕ", "value": "∑ i in Finset.range n, (i + 1)"}
    ],
    "goal": "2 * S = n * (n + 1)"
}

# CASE B: A "Weird" Problem (Putnam Style)
# Problem: "Define x * y = (x+y)/(1+xy). Find all x such that..."
# This requires custom notation that breaks the template structure.
weird_problem = {
    "problem_name": "putnam_weird_op",
    "raw_lean_override": """
-- Custom operator definition requires global scope, cannot fit in theorem args
def star_op (x y : ℝ) : ℝ := (x + y) / (1 + x * y)
infix:60 " ⋆ " => star_op

theorem putnam_weird_op (x : ℝ) (h : x ⋆ x = 1) : x = 1 := by
  sorry
""",
    "parameters": [],
    "definitions": [],
    "goal": ""
}

# ==========================================
# 3. EXECUTION
# ==========================================

if __name__ == "__main__":
    translator = LeanTranslator()

    print("--- OUTPUT 1: Standard Problem (Deterministic) ---")
    print(translator.render(standard_problem))
    print("\n" + "="*40 + "\n")

    print("--- OUTPUT 2: Weird Problem (Escape Hatch) ---")
    print(translator.render(weird_problem))