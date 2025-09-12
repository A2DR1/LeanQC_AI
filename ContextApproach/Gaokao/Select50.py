import numpy as np
import json

json_file = 'Gaokao-Formal_v3.json'
output_file = 'Gaokao-Formal_v3_50.txt'
test_file = 'Gaokao-Formal_v3_50_test.txt'

def load_data(json_file):
    # Load JSONL file (one JSON object per line)
    data = []
    with open(json_file, 'r') as f:
        for line in f:
            if line.strip():  # Skip empty lines
                data.append(json.loads(line))

    print(f"Total entries: {len(data)}")
    # print("First entry:")
    # print(data[0])
    return data

# -- BEGIN_PAIR {k}
# -- [Question]:
# -- {natural language statement, exactly as given}
# --
# -- [Lean 4]:
# /-- {one-line NL paraphrase or the exact question} -/
# theorem P{k}_{short_slug} {binders_if_any} : {formal_statement} := by sorry
# -- END_PAIR {k}

def Gaokao_save_data(data, output_file):
    index = 0
    with open(output_file, 'w') as f:
        for item in data[:50]:
            # Extract the theorem name from the formal_statement
            theorem_name = item['id']  # Use the ID as the theorem name
            formatted_item = f"-- BEGIN_PAIR {index}\n-- [Question]:\n-- {item['NL_English']}\n--\n-- [Lean 4]:\n/-- {item['formal_statement']}\n-- END_PAIR {index} \n\n"
            f.write(formatted_item + '\n')
            index += 1

def Gaokao_test_data(data, output_file):
    index = 0
    with open(output_file, 'w') as f:
        for item in data[50:100]:
            formatted_item = f"[NEW TASK]  \nNow, given a new [Question], translate it into a Lean 4 theorem statement following the **same style, formatting, and level of explicitness** as the examples above.  \n\n[Question]: {item['NL_English']}  "
            f.write(formatted_item + '\n' + '\n')
            index += 1

def main():
    data = load_data(json_file)

    # Gaokao_save_data(data, output_file)
    Gaokao_test_data(data, test_file)

if __name__ == "__main__":
    main()
