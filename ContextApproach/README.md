# Context Window Approach 

# Target LLM and their context windows:

- GPT-5o: ?
- GPT 4o: 128,000 tokens
- Gemini 1.5 pro: 2,000,000 tokens
- Gemini 2.5: 1,000,000 ~ 2,000,000 tokens
- Kimina-autoformalizer: ~ 32,000 tokens
- Goedel Prover: ~16,000 tokens
- Anthropic Claude 3 Sonnet: 200,000 tokens

# Context Template:

## Mathesis Template: 

\[Question\]:   
{statement}  

You are an expert in formal mathematics. Your task is to convert the above \[question\] to lean 4 theorems by completing the following lean 4 code:  

lean4   
import Mathlib   
import Aesop   
set-option maxHeartbeats 0   
set-option pp.numericTypes true   
set-option pp.coercions true   
set-option pp.letVarTypes true   
set-option pp.structureInstanceTypes true   
set-option pp.instanceTypes true   
set-option pp.mvars.withType true   
set-option pp.coercions true   
set-option pp.funBinderTypes true   
set-option pp.piBinderTypes true   
open BigOperators Real Nat Topology Rat  

{informal-comment}

## ATLAS Template:

You are an expert in the Lean4 theorem prover. Your task is to translate theorems from natural language into formal Lean4 statements. Please follow these guidelines:    
1\. Carefully analyze the given theorem in natural language.   
2\. Translate it into a correct and precise Lean4 formal statement.   
3\. Use the following format for your response: theorem tm\_name : The theorem’s Lean4 formal statement := by sorry   
4\. Focus solely on the translation. Do not attempt to prove the theorem or provide additional explanations.   
5\. Ensure that your translation accurately captures all the mathematical concepts and relationships expressed in the natural language version.   
6\. Use appropriate Lean4 syntax, including correct use of quantifiers, implications, and mathematical symbols.   
7\. If the theorem involves specific mathematical structures (e.g., groups, rings, topological spaces), use the corresponding Lean4 definitions and notations.  

Remember, the goal is to create a syntactically correct and semantically accurate formalization in Lean4. Your translation should be faithful to the meaning of the original theorem while adhering to Lean4 conventions and best practices.  

Now please begin by carefully reading the natural language statement provided, and then proceed with your translation into Lean4.   
{informal\_statement}

## Proposed Template 1: The LLM generate feedbacks for the NL-FL pair in the template. 

\[ROLE\]  
You are an expert in formal mathematics and Lean 4\. Translate each natural-language \[Question\] into a Lean 4 theorem \*\*statement\*\* that compiles. Do not prove it; end with \`:= by sorry\`. Do not add imports/options repeatedly; they are provided once below. Keep each theorem self-contained and faithful to the NL text.

\[GLOBAL LEAN CONTEXT — use once at the top of the output\]  
import Mathlib  
import Aesop  
set\_option maxHeartbeats 0  
set\_option pp.numericTypes true  
set\_option pp.coercions true  
set\_option pp.letVarTypes true  
set\_option pp.structureInstanceTypes true  
set\_option pp.instanceTypes true  
set\_option pp.mvars.withType true  
set\_option pp.funBinderTypes true  
set\_option pp.piBinderTypes true  
open scoped BigOperators  
open Real Nat Topology Rat Filter

\[FORMAT FOR EACH PAIR\]  
\-- BEGIN\_PAIR {k}  
\-- \[Question\]:  
\-- {natural language statement, exactly as given}  
\--  
\-- \[Lean 4\]:  
/-- {one-line NL paraphrase or the exact question} \-/  
theorem P{k}\_{short\_slug} {binders\_if\_any} : {formal\_statement} := by sorry  
\-- END\_PAIR {k}

\[NOTES\]  
\- Choose \`short\_slug\` from a few lowercase words (e.g., \`am\_gm\`, \`quad\_roots\`).  
\- Prefer explicit types for quantified vars (ℝ, ℕ, ℤ, ℚ, Matrix …).  
\- Use standard Mathlib names/notations (e.g., \`Real.sqrt\`, \`Nat.choose\`, \`∫ x in a..b, \_\`).

## Proposed Template 2:

import Mathlib  
import Aesop  
set\_option maxHeartbeats 0  
set\_option pp.numericTypes true  
set\_option pp.coercions true  
set\_option pp.letVarTypes true  
set\_option pp.structureInstanceTypes true  
set\_option pp.instanceTypes true  
set\_option pp.mvars.withType true  
set\_option pp.funBinderTypes true  
set\_option pp.piBinderTypes true  
open scoped BigOperators  
open Real Nat Topology Rat Filter

/-\! \#\# NL→FL pairs (50 items)  
Each block: NL question as a docstring \+ theorem skeleton.  
\-/

\-- BEGIN\_PAIR 1  
/-- \[Question\] Prove that if \`a \> 0\` and \`b \> 0\` then \`√(ab) ≤ (a+b)/2\`. \-/  
theorem P1\_am\_gm (a b : ℝ) (ha : 0 \< a) (hb : 0 \< b) :  
  Real.sqrt (a \* b) ≤ (a \+ b) / 2 := by sorry  
\-- END\_PAIR 1

\-- BEGIN\_PAIR 2  
/-- \[Question\] If \`x^2 \- 5x \+ 6 \= 0\`, then \`x \= 2 ∨ x \= 3\`. \-/  
theorem P2\_quad\_roots (x : ℝ) :  
  x ^ 2 \- 5 \* x \+ 6 \= 0 ↔ x \= 2 ∨ x \= 3 := by sorry  
\-- END\_PAIR 2

\-- … repeat up to 50

## Proposed Template 3:

[ROLE]  
You are an expert in formal mathematics and Lean 4.  
Your task is to translate each natural-language [Question] into a Lean 4 theorem **statement** that compiles.  
Do not attempt to prove it — always end with `:= by sorry`.  
Do not repeat the global imports/options. Use the provided global context.  
Keep each theorem self-contained and faithful to the natural-language text.  

[GLOBAL LEAN CONTEXT — always assumed at the top of the Lean file]  
import Mathlib  
import Aesop  
set_option maxHeartbeats 0  
set_option pp.numericTypes true  
set_option pp.coercions true  
set_option pp.letVarTypes true  
set_option pp.structureInstanceTypes true  
set_option pp.instanceTypes true  
set_option pp.mvars.withType true  
set_option pp.funBinderTypes true  
set_option pp.piBinderTypes true  
open scoped BigOperators  
open Real Nat Topology Rat Filter  

[EXAMPLES — use these as references for style and formatting]  

```
-- BEGIN_PAIR 1
-- [Question]:
-- Prove that if a > 0 and b > 0 then sqrt(ab) ≤ (a+b)/2.
--
-- [Lean 4]:
/-- AM–GM inequality for two positive reals. -/
theorem P1_am_gm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by sorry
-- END_PAIR 1

-- BEGIN_PAIR 2
-- [Question]:
-- If x^2 - 5x + 6 = 0, find all real solutions for x.
--
-- [Lean 4]:
/-- Solutions of the quadratic x² - 5x + 6 = 0. -/
theorem P2_quad_roots (x : ℝ) :
    x ^ 2 - 5 * x + 6 = 0 ↔ x = 2 ∨ x = 3 := by sorry
-- END_PAIR 2

-- BEGIN_PAIR 3
-- [Question]:
-- Show that ∑ k=1..n k = n(n+1)/2 for all natural n.
--
-- [Lean 4]:
/-- Closed form for the sum of the first n naturals. -/
theorem P3_sum_1_to_n (n : ℕ) :
    ∑ k in Finset.Icc 1 n, k = n * (n + 1) / 2 := by sorry
-- END_PAIR 3

...  
... continue up to 50 examples ...  
...

```

[NEW TASK]  
Now, given a new [Question], translate it into a Lean 4 theorem statement following the **same style, formatting, and level of explicitness** as the examples above.  

[Question]: {new natural-language theorem here}  

# NL-FL pairs

## ATLAS dataset and MathQual dataset:

Can't find it. Not sure if it is even posted.

## Mathesis dataset:

[https://github.com/Huawei-AI4Math/Mathesis/blob/main/Gaokao-Formal\_v3.json](https://github.com/Huawei-AI4Math/Mathesis/blob/main/Gaokao-Formal_v3.json) 

### Formatted input: 

./Gaokao-Formal_v3_50.txt

## LeanQC dataset:

To be collected.

## Lean-QuantumInfo dataset:

The theorems in Lean-QuantumInfo repositary are built based on a lot of homemade functions, so it is hard to feed the theorems to LLM with the current template. A different LLM prompt template may be needed, but this could potentially conflict with other dataset as they are not built based on the homemade functions. 