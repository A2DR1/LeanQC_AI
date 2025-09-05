#!/usr/bin/env python3
"""
Test script to check if read_prompts_from_txt function works correctly.
"""

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
    print("Testing read_prompts_from_txt function...")
    
    # Test with existing prompts.txt file
    txt_file_path = "prompts.txt"
    prompts = read_prompts_from_txt(txt_file_path)
    
    if prompts:
        print(f"✅ SUCCESS: Found {len(prompts)} prompts in {txt_file_path}")
        print("\nFirst 3 prompts:")
        for i, prompt in enumerate(prompts[:3], 1):
            print(f"  {i}. {prompt}")
        
        if len(prompts) > 3:
            print(f"  ... and {len(prompts) - 3} more prompts")
    else:
        print(f"❌ FAILED: No prompts found in {txt_file_path}")
    
    # Test with non-existent file
    print("\n" + "="*50)
    print("Testing with non-existent file...")
    fake_prompts = read_prompts_from_txt("nonexistent.txt")
    if not fake_prompts:
        print("✅ SUCCESS: Properly handled non-existent file")
    else:
        print("❌ FAILED: Should have returned empty list for non-existent file")

if __name__ == "__main__":
    main()
