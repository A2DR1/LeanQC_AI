import os
import sys
from pathlib import Path
import re
import json
from dotenv import load_dotenv
from openai import OpenAI
import importlib
from CNL_generation import CNL_generator # for reading CNL list
from tqdm import tqdm 
from lean_interact import LeanREPLConfig, LeanServer, Command, TempRequireProject, LeanRequire
import time
from eval_semantic import SemanticEvaluator

from config import models, STANDARD_IMPORTS, SYSTEM_PROMPT

# 1. Load environment variables
load_dotenv()


# create a FL_generator class
class FL_generator:
    def __init__(self, model_name="kimina_autoformalizer", dataset_name="miniF2F", isCNL=False, limit = 100):
        print(f"Initializing FL_generator with model '{model_name}' for dataset '{dataset_name}' (isCNL={isCNL}, limit={limit})...")
        # 1. Load model config
        self.dataset_name = dataset_name
        self.isCNL = isCNL
        self.limit = limit
        self.model = models.get(model_name, {})
        if not self.model:
            print(f"❌ Error: '{model_name}' config not found in config.py.")
            sys.exit(1)
        
        # from read_file.handle_miniF2F import readFolder_miniF2F
        handlerPath = "read_file.handle_" + dataset_name
        handlerName = dataset_name + "Handler"
        try:
            module = importlib.import_module(handlerPath)
            handlerClassRef = getattr(module, handlerName)
            self.handlerClass = handlerClassRef()
        except Exception as e:
            print(f"❌ Error importing dataset reader: {e}")
            sys.exit(1)

        # 2. Security Check
        self.api_key = self.model.get("api_key", "")
        if not self.api_key:
            print(f"❌ Error: API key for '{model_name}' not found in config.py.")
            sys.exit(1)

        # 3. Initialize Client
        try:
            self.client = OpenAI(api_key=self.api_key, base_url=self.model.get("base_url", ""))
        except Exception as e:
            print(f"❌ Error initializing client: {e}")
            sys.exit(1)

    def clean_lean_output(self, raw_text):
        """
        Cleans the LLM output to return *only* the code.
        Removes markdown backticks (```lean ... ```) and conversational filler.
        """
        # Remove markdown code blocks
        clean = re.sub(r"```lean\n", "", raw_text)
        clean = re.sub(r"```", "", clean)

        clean = clean.split("\n\n")[-1].strip()  # Take the last part after splitting by double newlines
        
        # If the model adds "Here is the code:", try to split and take the last part
        # (This is a heuristic, usually the code block handles it)
        return clean.strip()

    def generate_lean(self, cnl_statement, imports=STANDARD_IMPORTS, system_prompt=SYSTEM_PROMPT):
        """
        Autoformalizes a CNL/NL statement into a Lean 4 Theorem.
        """
        # print(f"🤖 Autoformalizing: '{cnl_statement[:50]}...'")

        user_prompt = f"""
        Context (Imports):
        {imports}

        Statement to Formalize:
        {cnl_statement}
        """

        try:
            response = self.client.chat.completions.create(
                model=self.model.get("model_name", ""),
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": user_prompt},
                ],
                temperature=0.2, # Low temp for syntax precision
                stream=False
            )
            
            raw_output = response.choices[0].message.content
            return self.clean_lean_output(raw_output)

        except Exception as e:
            return f"❌ API Error: {e}"

    def generate_write(self, input_path, name=None, json_output_path=None, CNL_model=None, semantic_judge_model=None):
        """
        Generate Lean formalizations for a list of statements.

        input_path can be:
        - a directory of miniF2F json files (readFolder_miniF2F)
        - a json file containing List[str] (read_cnl_lst)
        """
        print(f"📂 Processing: {input_path}")
        t0 = time.time()

        # ---------- Load statements ----------
        if not self.isCNL:
            # treat as dataset folder
            informal_statements = self.handlerClass.read(input_path, limit=self.limit)
        else:
            if not CNL_model:
                cnl_generator = CNL_generator()
            else:
                cnl_generator = CNL_generator(model_name=CNL_model)
            # treat as json file containing List[str]
            informal_statements = cnl_generator.read_cnl_lst(input_path)

        if not informal_statements:
            print("❌ No statements found.")
            return

        syntactic_corrects: list[bool] = []
        logs: list[str] = []
        semantic_corrects: list[bool] = []
        reasons: list[str] = []
        formal_statements: list[str] = []

        # ---------- Setup Lean server ----------
        project = TempRequireProject(lean_version="v4.8.0", require="mathlib")
        config = LeanREPLConfig(verbose=False, project=project)
        server = LeanServer(config)

        if not semantic_judge_model:
            semantic_evaluator = SemanticEvaluator()
        else:
            semantic_evaluator = SemanticEvaluator(model_name=semantic_judge_model)

        try:
            for statement in tqdm(informal_statements):
                lean_statement = self.generate_lean(statement)
                formal_statements.append(lean_statement)

                # --- Syntactic check ---
                resp = server.run(Command(cmd=STANDARD_IMPORTS + "\n\n" + lean_statement))

                # If ANY error message exists → fail
                error_msgs = [m for m in (resp.messages or []) if getattr(m, "severity", "") == "error"]
                if error_msgs:
                    is_syntactic_valid = False
                    # join all error messages for debugging
                    log = "\n".join([getattr(m, "data", str(m)) for m in error_msgs])
                else:
                    is_syntactic_valid = True
                    # include warnings if present
                    if resp.messages:
                        log = "\n".join([f"{m.severity}: {m.data}" for m in resp.messages])
                    else:
                        log = "No messages."

                syntactic_corrects.append(is_syntactic_valid)
                logs.append(log)

                # --- Semantic evaluation (only if syntactically valid) ---
                if is_syntactic_valid:
                    sem_eval = semantic_evaluator.evaluate_translation(statement, lean_statement)
                    is_correct = bool(sem_eval.get("is_correct", False))
                    reason = sem_eval.get("reason", "No reason provided.")
                else:
                    is_correct = False
                    reason = "Skipped semantic eval because syntactic check failed."

                semantic_corrects.append(is_correct)
                reasons.append(reason)

        except Exception as e:
            print(f"❌ Error during processing: {e}")

        n = len(informal_statements)

        # ---------- Write Lean file ----------
        if name:
            with open(name, "w", encoding="utf-8") as f:
                f.write(STANDARD_IMPORTS.strip() + "\n\n")
                for st in formal_statements:
                    f.write(st.strip() + "\n\n")

        # ---------- Write JSON file ----------
        if json_output_path:
            data = []
            for i in range(n):
                data.append({
                    "informal_statement": informal_statements[i],
                    "formal_statement": formal_statements[i],
                    "is_syntactically_correct": syntactic_corrects[i],
                    "syntactic_evaluation_log": logs[i],
                    "is_semantically_correct": semantic_corrects[i],
                    "semantic_evaluation_reason": reasons[i],
                })

            with open(json_output_path, "w", encoding="utf-8") as jf:
                json.dump(data, jf, indent=2, ensure_ascii=False)

        # ---------- Summary ----------
        syntax_accuracy = (sum(syntactic_corrects) / n) * 100 if n else 0.0

        syntactic_pass_idxs = [i for i, ok in enumerate(syntactic_corrects) if ok]
        semantic_filtered = [semantic_corrects[i] for i in syntactic_pass_idxs]
        semantic_accuracy = (sum(semantic_filtered) / len(semantic_filtered)) * 100 if semantic_filtered else 0.0

        print(f"\n✅ syntactic accuracy: {syntax_accuracy:.2f}% ({sum(syntactic_corrects)}/{n})")
        print(f"✅ semantic accuracy:  {semantic_accuracy:.2f}% ({sum(semantic_filtered)}/{len(semantic_filtered)})")
        print(f"⏱️ Total Time Spent: {time.time() - t0:.2f} seconds")

        return syntax_accuracy, semantic_accuracy
    
if __name__ == "__main__":
    generator = FL_generator(model_name="kimina_autoformalizer", dataset_name="miniF2F", isCNL=False, limit = 5)
    input_path = "testbench/MiniF2F/test"
    generator.generate_write(
        input_path,
        name="Autoformalized_miniF2F.lean",
        json_output_path="NL_FL_pairs_miniF2F.json"
    )