import os
import sys
from dotenv import load_dotenv
from openai import OpenAI
import json
from read_file.handle_miniF2F import readFolder

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


def generate_cnl_list(folder_path, limit=100, version=2):
    """
    Reads informal statements from JSON files in the specified folder,
    generates Controlled Natural Language (CNL) versions for each,
    and returns a list of CNL statements.
    """
    informal_statements = readFolder(folder_path, limit=limit)
    cnl_statements = []

    with open("cnl_rules.json", "r") as f:
        cnl_rules_data = json.load(f).get(f"v{version}", None)
        if cnl_rules_data is None:
            print(f"❌ Error: CNL rules for version {version} not found in cnl_rules.json.")
            return []
        cnl_rules = cnl_rules_data.get('rules', None)
        input_example = cnl_rules_data.get('example_input', None)
        output_example = cnl_rules_data.get('example_output', None)

    print(f"Using CNL rules: {cnl_rules[:50]}.")
    
    for statement in informal_statements:
        cnl = generate_cnl(statement, cnl_rules=cnl_rules,
                           input_example=input_example, output_example=output_example)
        cnl_statements.append(cnl)
    
    return cnl_statements

def read_cnl_lst(filename="cnl_statements.json"):
    """
    Reads a list of CNL statements from a specified json file.
    """
    with open(filename, 'r') as f:
        cnl_statements = json.load(f)
    return cnl_statements

def write_cnl_to_file(cnl_statements, filename="cnl_statements.json"):
    """
    Writes a list of CNL statements to a specified json file.
    """
    with open(filename, 'w') as f:
        json.dump(cnl_statements, f, indent=4)
    print(f"✅ Saved CNL statements to {filename}")

def generate_cnl(input_text, cnl_rules=None, input_example=None, output_example=None): 
    """
    Converts standard natural language into a Controlled Natural Language (CNL)
    based on a specific set of rules.
    """

    print("Generating Controlled Natural Language...")

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

    {
        "" if not input_example or not output_example else 
        f'''Here is an example of how to apply these rules:
        Input: {input_example}
        Output: {output_example}
        '''
    }

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

    cnl_statements = generate_cnl_list(folder_path, 100, version=4)
    write_cnl_to_file(cnl_statements, filename="cnl_statements_v4.json")

    