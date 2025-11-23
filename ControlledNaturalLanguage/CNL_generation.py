import os
import sys
from dotenv import load_dotenv
from openai import OpenAI

# Initialize the client using DeepSeek's base URL
# Ensure you have set your API key in your environment variables:
# export DEEPSEEK_API_KEY="sk-..."

print("Loading environment variables...")

load_dotenv()
api_key = os.getenv("DEEPSEEK_API_KEY")

client = OpenAI(
    api_key=api_key,  # Replace with your key string if not using env vars
    base_url="https://api.deepseek.com"
)

def generate_cnl(input_text, cnl_rules=None): 
    """
    Converts standard natural language into a Controlled Natural Language (CNL)
    based on a specific set of rules.
    """

    print("Generating Controlled Natural Language...")
    api_key=os.getenv("DEEPSEEK_API_KEY")
    print(f"key: {api_key}")
    
    # Default rules for a simple CNL (e.g., Simplified English)
    if cnl_rules is None:
        cnl_rules = (
            "1. Use only the present tense.\n"
            "2. Use active voice only (Subject + Verb + Object).\n"
            "3. Avoid ambiguous words like 'it', 'they', or 'thing'—be specific.\n"
            "4. One idea per sentence."
        )

    system_prompt = f"""
    You are a strict Controlled Natural Language (CNL) converter. 
    Your task is to rewrite the user's input text so that it adheres perfectly to the following rules:

    {cnl_rules}

    Output ONLY the rewritten text. Do not provide explanations or conversational filler.
    """

    try:
        response = client.chat.completions.create(
            model="deepseek-chat",
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": input_text},
            ],
            temperature=0.1, # Low temperature for deterministic, strictly compliant output
            stream=False
        )
        
        return response.choices[0].message.content.strip()

    except Exception as e:
        return f"Error generating CNL: {e}"

# --- Example Usage ---
if __name__ == "__main__":
    # Informal, complex input
    raw_text = (
        # "The server might have crashed because it was overloaded by too many requests "
        # "sent by the client, which is something that happens occasionally."
        "Let $x$, $y$ and $z$ all exceed $1$ and let $w$ be a positive number such that $\\log_x w = 24$, $\\log_y w = 40$ and $\\log_{xyz} w = 12$. Find $\\log_z w$. Show that it is 060."
    )

    print(f"--- Original Text ---\n{raw_text}\n")
    
    # Convert to CNL
    cnl_output = generate_cnl(raw_text)
    
    print(f"--- Controlled Natural Language Output ---\n{cnl_output}")