import os
import sys
import re
import json
from dotenv import load_dotenv
from openai import OpenAI
from config import models

# 1. Load environment variables
load_dotenv()

class SemanticEvaluator:
    def __init__(self, model_name="deepseek-R1"):
        print(f"Initializing SemanticEvaluator with model '{model_name}'...")
        self.client, self.model = self.initialize_client(model_name)

    def initialize_client(self, model_name="deepseek-R1"):
        model = models.get(model_name, None)
        if model is None:
            print(f"❌ Error: Model '{model_name}' not found in config.py.")
            print(f"Available models: {list(models.keys())}")
            print("current models config:", models.get(model_name, None))
            sys.exit(1)
        # 2. Security Check
        api_key = model.get("api_key", None)
        if not api_key:
            print("❌ Error: DEEPSEEK_API_KEY not found in .env file.")
            sys.exit(1)

        # 3. Initialize Client
        try:
            client = OpenAI(api_key=api_key, base_url=model.get("base_url", "" ))
        except Exception as e:
            print(f"❌ Error initializing client: {e}")
            sys.exit(1)

        return client, model


    def evaluate_translation(self, english_text, lean_code):
        """
        Uses an LLM to judge if the Lean code semantically matches the English text.
        """
        judge_prompt = f"""
        You are an expert Mathematics Formalization Judge.
        Your task is to evaluate if a generated Lean 4 theorem accurately captures the **mathematical intent** of a natural language statement.
        
        1. **Ignore Proofs:** The body `:= sorry` or `by ...` is irrelevant. Judge ONLY the theorem signature (assumptions & goal).
        
        2. **Strict Type/Logic Checks:**
        - Ensure variable types match (e.g., 'integer' $\to$ `Int` or `Nat`, not `Real`).
        - Ensure constraints are present (e.g., 'positive' $\to$ `x > 0`).
        - Ensure the logical implication flows correctly (Hypothesis $\to$ Conclusion).

        3. **ALLOW FORMAT ADAPTATIONS (Critical):**
        - **Questions $\to$ Theorems:** If the English asks "What is X?", the Lean code MUST provide the answer in the statement (e.g., `theorem value_is_5 : X = 5`). This is **CORRECT** behavior, not a hallucination.
        - **Imperatives $\to$ Declaratives:** "Find the maximum" $\to$ `theorem is_maximum ...`.
        - **Implicit Context:** If the English implies standard definitions (e.g., "primes"), the Lean code may make them explicit.

        4. **FAIL CRITERIA (Mark as False if):**
        - The Lean theorem proves a *different* mathematical fact (e.g., English asks for `Sum`, Lean proves `Product`).
        - The Lean theorem simplifies the problem significantly (e.g., dropping hard constraints).
        - The types are fundamentally wrong (e.g., treating a Matrix as a Real number).
        Input English: "{english_text}"
        Generated Lean: "{lean_code}"

        Answer with JSON only:
        {{
            "reason": "Short explanation of the error or 'Correct'",
            "is_correct": true/false,
        }}
        """

        try:
            response = self.client.chat.completions.create(
                model=self.model.get("model_name"),
                messages=[{"role": "user", "content": judge_prompt}],
                response_format={"type": "json_object"},
                temperature=0.0
            )
            return json.loads(response.choices[0].message.content)
        except Exception as e:
            return {"is_correct": False, "reason": f"Judge Error: {e}"}