#!/usr/bin/env python3
"""
Create a prompt-ready version of the repository content.
This version includes actual file content in a clean format suitable for AI prompts.
"""

import re
from pathlib import Path

def create_prompt_version(input_file: str, output_file: str):
    """Create a prompt-ready version of the repository content."""
    
    with open(input_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Split into sections by file headers
    sections = content.split('=' * 80)
    
    prompt_content = []
    prompt_content.append("LEAN-QUANTUMINFO REPOSITORY CONTENT")
    prompt_content.append("Repository: https://github.com/Timeroot/Lean-QuantumInfo.git")
    prompt_content.append("=" * 60)
    prompt_content.append("")
    
    file_count = 0
    
    for i, section in enumerate(sections[1:], 1):  # Skip the first empty section
        if not section.strip():
            continue
            
        lines = section.strip().split('\n')
        if len(lines) < 3:
            continue
            
        # Extract file info
        file_line = lines[0].strip()
        type_line = lines[1].strip()
        
        if file_line.startswith('FILE:'):
            file_path = file_line.replace('FILE:', '').strip()
            file_type = type_line.replace('TYPE:', '').strip()
            
            # Find the content after the separator line
            content_start = 0
            for j, line in enumerate(lines):
                if line.strip() == '=' * 80:
                    content_start = j + 1
                    break
            
            if content_start < len(lines):
                content_lines = lines[content_start:]
                
                # Clean up the content
                cleaned_content = []
                for line in content_lines:
                    line = line.rstrip()
                    cleaned_content.append(line)
                
                # Remove trailing empty lines
                while cleaned_content and not cleaned_content[-1].strip():
                    cleaned_content.pop()
                
                # Only include if there's actual content
                if cleaned_content and any(line.strip() for line in cleaned_content):
                    prompt_content.append(f"## File: {file_path} ({file_type})")
                    prompt_content.append("```")
                    prompt_content.extend(cleaned_content)
                    prompt_content.append("```")
                    prompt_content.append("")
                    file_count += 1
    
    # Write prompt version
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write('\n'.join(prompt_content))
    
    print(f"Prompt version created: {output_file}")
    print(f"Files included: {file_count}")
    print(f"Total size: {len('\n'.join(prompt_content))} characters")

if __name__ == "__main__":
    input_file = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_full_content.txt"
    output_file = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_prompt.txt"
    
    create_prompt_version(input_file, output_file)
