from openai import OpenAI

client = OpenAI(
  base_url="https://api.featherless.ai/v1",
  api_key="rc_f32286f75d3df30fb4dded2835029af9126f0d66187cae807bdd6dfbe61f83a2",
)

response = client.chat.completions.create(
  model='ByteDance-Seed/BFS-Prover-V1-7B',
  messages=[
    {"role": "system", "content": "You are a helpful assistant."},
    {"role": "user", "content": "Hello!"}
  ],
)
print(response.model_dump()['choices'][0]['message']['content'])
