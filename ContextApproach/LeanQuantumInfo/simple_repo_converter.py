#!/usr/bin/env python3
"""
Simple repository to text converter that directly processes files.
This creates a clean, prompt-ready version of the repository content.
"""

import os
from pathlib import Path

def convert_repo_to_text(repo_path: str, output_file: str):
    """Convert all files in the repository to a single text file."""
    
    repo_path = Path(repo_path)
    content = []
    
    # Header
    content.append("LEAN-QUANTUMINFO REPOSITORY CONTENT")
    content.append("Repository: https://github.com/Timeroot/Lean-QuantumInfo.git")
    content.append("=" * 60)
    content.append("")
    
    file_count = 0
    
    # File extensions to include
    included_extensions = {
        '.lean', '.md', '.txt', '.json', '.yaml', '.yml', 
        '.py', '.sh', '.bat', '.cfg', '.conf', '.ini'
    }
    
    # Directories to skip
    skip_dirs = {'.git', 'node_modules', '__pycache__', '.pytest_cache'}
    
    def should_skip_file(file_path):
        # Skip if in a directory we want to skip
        for part in file_path.parts:
            if part in skip_dirs:
                return True
        # Skip if extension not included
        if file_path.suffix.lower() not in included_extensions:
            return True
        return False
    
    def read_file_safely(file_path):
        """Safely read a file with proper encoding handling."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                return f.read()
        except UnicodeDecodeError:
            try:
                with open(file_path, 'r', encoding='latin-1') as f:
                    return f.read()
            except:
                return f"[ERROR: Could not read file]"
        except:
            return f"[ERROR: Could not read file]"
    
    def process_file(file_path):
        nonlocal file_count
        if should_skip_file(file_path):
            return
            
        try:
            file_content = read_file_safely(file_path)
            relative_path = file_path.relative_to(repo_path)
            
            # Add file header and content
            content.append(f"## File: {relative_path}")
            content.append("```")
            content.append(file_content)
            content.append("```")
            content.append("")
            
            file_count += 1
            print(f"Processed: {relative_path}")
            
        except Exception as e:
            print(f"Error processing {file_path}: {e}")
    
    def process_directory(directory):
        """Recursively process all files in a directory."""
        try:
            for item in sorted(directory.iterdir()):
                if item.is_file():
                    process_file(item)
                elif item.is_dir():
                    if not any(part in skip_dirs for part in item.parts):
                        process_directory(item)
        except PermissionError as e:
            print(f"Permission denied accessing {directory}: {e}")
        except Exception as e:
            print(f"Error processing directory {directory}: {e}")
    
    # Process all files
    process_directory(repo_path)
    
    # Add summary
    content.append("=" * 60)
    content.append(f"SUMMARY: Processed {file_count} files")
    content.append("=" * 60)
    
    # Write to output file
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write('\n'.join(content))
    
    print(f"\nConversion completed!")
    print(f"Files processed: {file_count}")
    print(f"Output saved to: {output_file}")

if __name__ == "__main__":
    repo_path = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/Lean-QuantumInfo"
    output_file = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_simple.txt"
    
    convert_repo_to_text(repo_path, output_file)
