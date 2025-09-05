# Context Window Approach 

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

## Proposed Template 1:

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

# NL-FL pairs

## ATLAS dataset and MathQual dataset:

## Mathesis dataset:

[https://github.com/Huawei-AI4Math/Mathesis/blob/main/Gaokao-Formal\_v3.json](https://github.com/Huawei-AI4Math/Mathesis/blob/main/Gaokao-Formal_v3.json) 

### Formatted input: 

./Gaokao-Formal_v3_50.txt

## LeanQC dataset:

## Lean-QuantumInfo dataset: