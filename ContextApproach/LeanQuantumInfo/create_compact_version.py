#!/usr/bin/env python3
"""
Create a compact version of the repository content for prompt use.
This version removes excessive whitespace and formatting while preserving structure.
"""

import re
from pathlib import Path

def create_compact_version(input_file: str, output_file: str):
    """Create a more compact version of the repository content."""
    
    with open(input_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Split into sections by file headers
    sections = content.split('=' * 80)
    
    compact_content = []
    compact_content.append("LEAN-QUANTUMINFO REPOSITORY CONTENT (COMPACT VERSION)")
    compact_content.append("=" * 60)
    compact_content.append("")
    
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
            
            # Get the actual content (skip the header lines)
            # Find the content after the separator line
            content_start = 0
            for j, line in enumerate(lines):
                if line.strip() == '=' * 80:
                    content_start = j + 1
                    break
            content_lines = lines[content_start:]
            
            # Clean up the content
            cleaned_content = []
            for line in content_lines:
                # Remove excessive whitespace but preserve structure
                line = line.rstrip()
                if line.strip():  # Keep non-empty lines
                    cleaned_content.append(line)
                elif cleaned_content and cleaned_content[-1].strip():  # Keep single empty lines
                    cleaned_content.append('')
            
            # Remove trailing empty lines
            while cleaned_content and not cleaned_content[-1].strip():
                cleaned_content.pop()
            
            # Add to compact content
            compact_content.append(f"--- {file_path} ({file_type}) ---")
            compact_content.extend(cleaned_content)
            compact_content.append("")
    
    # Write compact version
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write('\n'.join(compact_content))
    
    print(f"Compact version created: {output_file}")
    print(f"Original size: {len(content)} characters")
    print(f"Compact size: {len('\n'.join(compact_content))} characters")
    print(f"Compression ratio: {len('\n'.join(compact_content)) / len(content):.2%}")

if __name__ == "__main__":
    input_file = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_full_content.txt"
    output_file = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_compact.txt"
    
    create_compact_version(input_file, output_file)
