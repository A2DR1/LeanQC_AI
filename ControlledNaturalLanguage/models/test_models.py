from openai import OpenAI
from dotenv import load_dotenv
import os



# The URL from your Modal deployment
# client = OpenAI(
#     base_url="https://austinszj--kimina-autoformalizer-vllm-inference-serve.modal.run/v1",
#     api_key="EMPTY"  # vLLM doesn't require a key by default
# )

load_dotenv()  # Load environment variables from .env file

# client = OpenAI(
#     base_url="https://api.fireworks.ai/inference/v1",
#     api_key=os.getenv("FIREWORK_API_KEY")
# )  # Uses environment variables for configuration

# "deepseek-prover-v2": {
#         "model_name": "deepseek-ai/DeepSeek-Prover-V2-671B:novita",
#         "base_url": "https://router.huggingface.co/v1",
#         "api_key": os.environ.get("HF_TOKEN"),
#     }

client = OpenAI(
    base_url="https://router.huggingface.co/v1",
    api_key=os.getenv("HF_TOKEN")
)

informal_statement = "Let $x$, $y$ and $z$ all exceed $1$ and let $w$ be a positive number such that $\\log_x w = 24$, $\\log_y w = 40$ and $\\log_{xyz} w = 12$. Find $\\log_z w$. Show that it is 060."
# print("Informal Statement:", informal_statement)

template = """Translate the following informal mathematical statement into Lean 4 code using Mathlib, end the theorem with 'sorry'.
Do not import any modules, just provide the theorem statement.
"""

response = client.chat.completions.create(
    model="deepseek-ai/DeepSeek-Prover-V2-671B:novita",
    messages=[
        {"role": "system", "content": template},
        {"role": "user", "content": informal_statement}
        ],
    max_tokens=256
)

print(response.choices[0].message.content.split("\n\n")[-1].strip())  # Print only the code block