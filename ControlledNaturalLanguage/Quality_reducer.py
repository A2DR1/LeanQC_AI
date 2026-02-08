from config import models, DEGRADER_PROMPT
from openai import OpenAI
import sys

class qualityReducer:
    def __init__(self, model_name="deepseek-chat"):
        print(f"Initializing qualityReducer with model '{model_name}'...")
        self.model = models.get(model_name, None)
        if self.model is None:
            print(f"❌ Error: Model '{model_name}' not found in configuration.")
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

    def reduce_quality(self, clean_statement):
        """
        Uses the specified model to degrade the quality of the given Lean code.
        """
        prompt = DEGRADER_PROMPT.format(clean_statement=clean_statement)
        
        try:
            response = self.client.chat.completions.create(
                model=self.model.get("model_name"),
                messages=[
                    {"role": "system", "content": "You are a code quality degrader."},
                    {"role": "user", "content": prompt}
                ],
                max_tokens=1000,
                temperature=0.7,
            )
            degraded_code = response.choices[0].message.content.strip()
            return degraded_code
        except Exception as e:
            print(f"❌ Error during quality reduction: {e}")
            return None
        
if __name__ == "__main__":
    # Example usage
    reducer = qualityReducer(model_name="deepseek-chat")
    clean_nl_statement = "Let $x$, $y$ and $z$ all exceed $1$ and let $w$ be a positive number such that $\\log_x w = 24$, $\\log_y w = 40$ and $\\log_{xyz} w = 12$. Find $\\log_z w$. Show that it is 060."
    print("Original Clean Statement:\n", clean_nl_statement)
    degraded_statement = reducer.reduce_quality(clean_statement=clean_nl_statement)
    print("Degraded Statement:\n", degraded_statement)