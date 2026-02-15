import os
import sys
from dotenv import load_dotenv
from openai import OpenAI
import importlib
import json
from read_file.handle_miniF2F import miniF2FHandler
from config import models
import re

# Initialize the client using DeepSeek's base URL
# Ensure you have set your API key in your environment variables:
# export DEEPSEEK_API_KEY="sk-..."


class CNL_generator:
    def __init__(self, benchmark_name="miniF2F", cnl_rules_path="cnl_rules.json", model_name="deepseek-prover-v2"):
        print(f"Initializing CNL_generator for benchmark '{benchmark_name}' using model '{model_name}'...")
        self.benchmark_name = benchmark_name
        self.cnl_rules_path = cnl_rules_path

        self.model = models.get(model_name, None)
        if self.model is None:
            print(f"❌ Error: Model '{self.model_name}' not found in config.py.")
            sys.exit(1)

        try:
            self.client = OpenAI(
                api_key=self.model.get("api_key"),  # Replace with your key string if not using env vars
                base_url=self.model.get("base_url", "")
            )
        except Exception as e:
            print(f"❌ Error initializing OpenAI client: {e}")
            print(f"Current api_key: {self.model.get('api_key')}")
            print(f"Current base_url: {self.model.get('base_url', '')}")
            sys.exit(1)

        # from read_file.handle_miniF2F import readFolder_miniF2F
        handlerPath = "read_file.handle_" + benchmark_name
        handlerName = benchmark_name + "Handler"
        try:
            module = importlib.import_module(handlerPath)
            handlerClassRef = getattr(module, handlerName)
            self.handlerClass = handlerClassRef()
        except Exception as e:
            print(f"❌ Error importing dataset reader: {e}")
            sys.exit(1)
        

    def generate_cnl_list(self, folder_path, limit=100, version=2):
        """
        Reads informal statements from JSON files in the specified folder,
        generates Controlled Natural Language (CNL) versions for each,
        and returns a list of CNL statements.
        """
        
        informal_statements = self.handlerClass.read(folder_path, limit=limit)
        print(f"Read {len(informal_statements)} informal statements from {folder_path}.")
        cnl_statements = []

        with open(self.cnl_rules_path, "r") as f:
            cnl_rules_data = json.load(f).get(f"v{version}", None)
            if cnl_rules_data is None:
                print(f"❌ Error: CNL rules for version {version} not found in cnl_rules.json.")
                return []
            cnl_rules = cnl_rules_data.get('rules', None)
            input_example = cnl_rules_data.get('example_input', None)
            output_example = cnl_rules_data.get('example_output', None)

        print(f"Using CNL rules: {cnl_rules[:50]}.")
        
        for statement in informal_statements:
            cnl = self.generate_cnl(statement, cnl_rules=cnl_rules,
                            input_example=input_example, output_example=output_example)
            cnl_statements.append(cnl)
        
        return cnl_statements

    def read_cnl_lst(self, filename="cnl_statements.json"):
        """
        Reads a list of CNL statements from a specified json file.
        """
        with open(filename, 'r') as f:
            cnl_statements = json.load(f)
        return cnl_statements

    def write_cnl_to_file(self, cnl_statements, filename="cnl_statements.json"):
        """
        Writes a list of CNL statements to a specified json file.
        """
        with open(filename, 'w') as f:
            json.dump(cnl_statements, f, indent=4)
        print(f"✅ Saved CNL statements to {filename}")

    def generate_cnl(self, input_text, cnl_rules=None, input_example=None, output_example=None): 
        """
        Converts standard natural language into a Controlled Natural Language (CNL)
        based on a specific set of rules.
        """

        # print("Generating Controlled Natural Language...")

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
            response = self.client.chat.completions.create(
                model=self.model.get("model_name"),
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": input_text},
                ],
                temperature=0.1, # Low temperature for deterministic, strictly compliant output
                stream=False
            )
            
            return self.strip_cnl_extras(response.choices[0].message.content.strip())

        except Exception as e:
            return f"Error generating CNL: {e}"
            
    def strip_cnl_extras(self, cnl_text):
        """
        Strips any extraneous explanations or comments from the CNL text,
        returning only the core CNL statement.
        """
        # For this example, we assume the CNL text is clean.
        # Implement any specific stripping logic if needed.
        cnl_text = re.sub(r'<think>.*?</think>', '', cnl_text, flags=re.DOTALL)
        return cnl_text.strip()
    
def strip_cnl_extras(cnl_text):
        """
        Strips any extraneous explanations or comments from the CNL text,
        returning only the core CNL statement.
        """
        # For this example, we assume the CNL text is clean.
        # Implement any specific stripping logic if needed.
        cnl_text = re.sub(r'<think>.*?</think>', '', cnl_text, flags=re.DOTALL)
        return cnl_text.strip()

def read_cnl_lst(filename="cnl_statements.json"):
        """
        Reads a list of CNL statements from a specified json file.
        """
        with open(filename, 'r') as f:
            cnl_statements = json.load(f)
        return cnl_statements

# --- Example Usage ---
if __name__ == "__main__":
    miniF2F_cnl_gen = CNL_generator(benchmark_name="Putnam", cnl_rules_path="cnl_rules.json", model_name="deepseek-prover-v2")
    cnl_statements = miniF2F_cnl_gen.generate_cnl_list("testbench/Putnam/putnam.json", 5, version=8)
    miniF2F_cnl_gen.write_cnl_to_file(cnl_statements, filename="test_cnl_statements_v8.json")

    