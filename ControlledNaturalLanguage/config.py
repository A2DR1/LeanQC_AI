import os

models = {
    "kimina_autoformalizer": {
        "model_name": "AI-MO/Kimina-Autoformalizer-7B",
        "base_url": "https://austinszj--kimina-autoformalizer-vllm-inference-serve.modal.run/v1",
        "api_key": "EMPTY",  # vLLM doesn't require a key by default
        "model_revision": "ddd47cb",
    },
    "deepseek_chat": {
        "model_name": "deepseek-chat",
        "base_url": "https://api.deepseek.com",
        "api_key": os.getenv("DEEPSEEK_API_KEY")
    },
}