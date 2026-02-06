from dotenv import load_dotenv
import os
from openai import OpenAI

load_dotenv()

# endpoint = "https://austinszj-3211-resource.openai.azure.com/openai/v1"
# deployment_name = "DeepSeek-R1"
# api_key = os.environ.get("FOUNDARY_API_KEY")

# client = OpenAI(
#     base_url=endpoint,
#     api_key=api_key
# )

# completion = client.chat.completions.create(
#     model=deployment_name,
#     messages=[
#         {
#             "role": "user",
#             "content": "What is the capital of France?",
#         }
#     ],
# )

# print(completion.choices[0].message)


endpoint = "https://austinszj-3211-resource.openai.azure.com/openai/v1"
deployment_name = "DeepSeek-V3-0324"
api_key = os.environ.get("FOUNDARY_API_KEY")

client = OpenAI(
    base_url=endpoint,
    api_key=api_key
)

completion = client.chat.completions.create(
    model=deployment_name,
    messages=[
        {
            "role": "user",
            "content": "What is the capital of France?",
        }
    ],
)

print(completion.choices[0].message)