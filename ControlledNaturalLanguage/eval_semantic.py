import os
import sys
import re
import json
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


def evaluate_translation(english_text, lean_code):
    """
    Uses an LLM to judge if the Lean code semantically matches the English text.
    """
    judge_prompt = f"""
    You are a strict mathematics judge. 
    Your task is to evaluate if a piece of Lean 4 code accurately captures the meaning of a natural language mathematical statement.

    1. Ignore missing proofs (e.g., ':= sorry' is acceptable).
    2. Focus on the THEOREM STATEMENT (assumptions, types, and goal).
    3. Check for:
       - Missing assumptions (e.g., English says "x is positive", Lean misses `x > 0`).
       - Wrong types (e.g., English says "integer", Lean uses `Real`).
       - Incorrect logical operators (e.g., "and" vs "implies").

    Input English: "{english_text}"
    Generated Lean: "{lean_code}"

    Answer with JSON only:
    {{
        "is_correct": true/false,
        "reason": "Short explanation of the error or 'Correct'"
    }}
    """

    try:
        response = client.chat.completions.create(
            model="deepseek-chat", # Or GPT-4o if you want a stronger external judge
            messages=[{"role": "user", "content": judge_prompt}],
            response_format={"type": "json_object"},
            temperature=0.0
        )
        return json.loads(response.choices[0].message.content)
    except Exception as e:
        return {"is_correct": False, "reason": f"Judge Error: {e}"}