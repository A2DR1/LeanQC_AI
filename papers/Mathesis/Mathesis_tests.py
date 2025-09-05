from llama_cpp import Llama
import os

# Load your model (CPU only for stability)
llm = Llama(
    model_path="Mathesis-Autoformalizer-HPO.Q4_K_M.gguf",
    n_ctx=4096,           # Context length (max tokens in prompt + output)
    n_threads=8,          # Number of CPU threads to use (match your CPU cores/threads)
    n_batch=512,          # Batch size for prompt processing
    n_threads_batch=8,    # Threads for batch processing (optional)
    use_mlock=True,       # Lock model in RAM to avoid swapping
    numa=False            # Keep this False unless on multi-socket servers
)

max_tokens = 500

def test_prompt(prompt):
    """Send a single prompt to the model."""
    output = llm(prompt, max_tokens=max_tokens)
    return output

def read_prompts_from_txt(txt_file_path):
    """Read prompts from a plain text file, one per line."""
    prompts = []
    try:
        with open(txt_file_path, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line:  # skip empty lines
                    prompts.append(line)
    except FileNotFoundError:
        print(f"Error: File '{txt_file_path}' not found.")
    except Exception as e:
        print(f"Error reading file: {e}")
    return prompts

def main():
    # File paths
    txt_file_path = "prompts.txt"        # Input prompts file
    results_file_path = "results.txt"    # Output results file
    
    # Load prompts
    prompts = read_prompts_from_txt(txt_file_path)
    
    if not prompts:
        print("No prompts found in the text file.")
        return
    
    print(f"Found {len(prompts)} prompts in the text file.")
    
    # Open results file for writing
    with open(results_file_path, 'w', encoding='utf-8') as results_file:
        results_file.write("Mathesis Model Test Results\n")
        results_file.write("=" * 50 + "\n\n")
        
        # Test each prompt
        for i, prompt in enumerate(prompts, 1):
            print(f"\n--- Testing Prompt {i} ---")
            print(f"Prompt: {prompt}")
            
            results_file.write(f"--- Prompt {i} ---\n")
            results_file.write(f"Input: {prompt}\n")
            
            try:
                result = test_prompt(prompt)
                output_text = result['choices'][0]['text']
                print(f"Output: {output_text}")
                
                results_file.write(f"Output: {output_text}\n")
                results_file.write("-" * 30 + "\n\n")
            
            except Exception as e:
                error_msg = f"Error processing prompt: {e}"
                print(error_msg)
                
                results_file.write(f"Error: {error_msg}\n")
                results_file.write("-" * 30 + "\n\n")
    
    print(f"\nResults have been written to: {results_file_path}")

if __name__ == "__main__":
    main()
    import gc
    del llm      # Delete model object
    gc.collect() # Force Python to free memory