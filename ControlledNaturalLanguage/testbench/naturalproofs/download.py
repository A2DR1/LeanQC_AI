import requests
import json
import os
from tqdm import tqdm

def peek_json(filename, num_items=1):
    print(f"\n🔍 Inspecting first {num_items} items...")
    
    try:
        with open(filename, 'r', encoding='utf-8') as f:
            data = json.load(f)
            print(f"Keys: {list(data.keys())}")

            dataset = data.get("dataset", [])
            print(f"Dataset Keys: {dataset.keys()}")

            thorems = dataset.get("theorems", [])
            print(f"Total theorems: {len(thorems)}")
            print(f"First theorem: {thorems[0]}")
                
    except Exception as e:
        print(f"❌ Error: {e}")

if __name__ == "__main__":
    # Step 1: Download
    output_filename = "naturalproofs_proofwiki.json"
    peek_json(output_filename)