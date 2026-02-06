from openai import OpenAI

# The URL from your Modal deployment
client = OpenAI(
    base_url="https://austinszj--kimina-autoformalizer-vllm-inference-serve.modal.run/v1",
    api_key="EMPTY"  # vLLM doesn't require a key by default
)

informal_statement = "Let $x$, $y$ and $z$ all exceed $1$ and let $w$ be a positive number such that $\\log_x w = 24$, $\\log_y w = 40$ and $\\log_{xyz} w = 12$. Find $\\log_z w$. Show that it is 060."
print("Informal Statement:", informal_statement)

template = """Translate the following informal mathematical statement into Lean 4 code using Mathlib, end the theorem with 'sorry'.:
{informal_statement}
""".format(informal_statement=informal_statement)

response = client.chat.completions.create(
    model="AI-MO/Kimina-Autoformalizer-7B",
    messages=[{"role": "user", 
               "content": template}],
    max_tokens=256
)

print(response.choices[0].message.content)