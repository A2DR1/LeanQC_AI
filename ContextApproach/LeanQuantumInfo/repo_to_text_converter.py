#!/usr/bin/env python3
"""
Repository to Text Converter
Converts all files from the Lean-QuantumInfo repository to a single text format suitable for prompts.
"""

import os
import sys
from pathlib import Path
import mimetypes
from typing import List, Tuple

class RepoToTextConverter:
    def __init__(self, repo_path: str, output_file: str = "repository_content.txt"):
        self.repo_path = Path(repo_path)
        self.output_file = output_file
        self.text_content = []
        self.file_count = 0
        self.skipped_files = []
        
        # File extensions to include (add more as needed)
        self.included_extensions = {
            '.lean', '.md', '.txt', '.json', '.yaml', '.yml', 
            '.py', '.sh', '.bat', '.cfg', '.conf', '.ini',
            '.c', '.cpp', '.h', '.hpp', '.java', '.js', '.ts',
            '.html', '.css', '.xml', '.sql', '.r', '.m', '.hs'
        }
        
        # Files to skip
        self.skip_files = {
            '.gitignore', '.gitattributes', '.DS_Store', 'Thumbs.db',
            'node_modules', '.git', '__pycache__', '.pytest_cache',
            '*.pyc', '*.pyo', '*.pyd', '*.so', '*.dll', '*.exe'
        }
        
        # Directories to skip
        self.skip_dirs = {
            '.git', 'node_modules', '__pycache__', '.pytest_cache',
            '.vscode', '.idea', 'build', 'dist', 'target'
        }

    def should_skip_file(self, file_path: Path) -> bool:
        """Check if a file should be skipped."""
        # Skip if file name is in skip list
        if file_path.name in self.skip_files:
            return True
            
        # Skip if file extension is not in included list
        if file_path.suffix.lower() not in self.included_extensions:
            return True
            
        # Skip if file is in a directory we want to skip
        for part in file_path.parts:
            if part in self.skip_dirs:
                return True
                
        return False

    def get_file_type(self, file_path: Path) -> str:
        """Determine file type for better formatting."""
        suffix = file_path.suffix.lower()
        
        type_mapping = {
            '.lean': 'Lean 4',
            '.md': 'Markdown',
            '.txt': 'Text',
            '.json': 'JSON',
            '.yaml': 'YAML',
            '.yml': 'YAML',
            '.py': 'Python',
            '.sh': 'Shell Script',
            '.bat': 'Batch Script',
            '.cfg': 'Configuration',
            '.conf': 'Configuration',
            '.ini': 'Configuration',
            '.c': 'C',
            '.cpp': 'C++',
            '.h': 'C Header',
            '.hpp': 'C++ Header',
            '.java': 'Java',
            '.js': 'JavaScript',
            '.ts': 'TypeScript',
            '.html': 'HTML',
            '.css': 'CSS',
            '.xml': 'XML',
            '.sql': 'SQL',
            '.r': 'R',
            '.m': 'MATLAB/Objective-C',
            '.hs': 'Haskell'
        }
        
        return type_mapping.get(suffix, 'Unknown')

    def read_file_safely(self, file_path: Path) -> str:
        """Safely read a file with proper encoding handling."""
        try:
            # Try UTF-8 first
            with open(file_path, 'r', encoding='utf-8') as f:
                return f.read()
        except UnicodeDecodeError:
            try:
                # Try latin-1 as fallback
                with open(file_path, 'r', encoding='latin-1') as f:
                    return f.read()
            except Exception as e:
                return f"[ERROR: Could not read file - {str(e)}]"
        except Exception as e:
            return f"[ERROR: Could not read file - {str(e)}]"

    def process_file(self, file_path: Path) -> None:
        """Process a single file and add it to the text content."""
        if self.should_skip_file(file_path):
            return
            
        try:
            content = self.read_file_safely(file_path)
            file_type = self.get_file_type(file_path)
            relative_path = file_path.relative_to(self.repo_path)
            
            # Add file header
            self.text_content.append(f"\n{'='*80}")
            self.text_content.append(f"FILE: {relative_path}")
            self.text_content.append(f"TYPE: {file_type}")
            self.text_content.append(f"SIZE: {len(content)} characters")
            self.text_content.append(f"{'='*80}\n")
            
            # Add file content
            self.text_content.append(content)
            
            self.file_count += 1
            print(f"Processed: {relative_path}")
            
        except Exception as e:
            error_msg = f"[ERROR processing {file_path}: {str(e)}]"
            self.text_content.append(error_msg)
            self.skipped_files.append((str(file_path), str(e)))
            print(f"Error processing {file_path}: {e}")

    def process_directory(self, directory: Path) -> None:
        """Recursively process all files in a directory."""
        try:
            for item in sorted(directory.iterdir()):
                if item.is_file():
                    self.process_file(item)
                elif item.is_dir():
                    # Check if directory should be skipped
                    if not any(part in self.skip_dirs for part in item.parts):
                        self.process_directory(item)
        except PermissionError as e:
            print(f"Permission denied accessing {directory}: {e}")
        except Exception as e:
            print(f"Error processing directory {directory}: {e}")

    def generate_summary(self) -> str:
        """Generate a summary of the conversion process."""
        summary = [
            f"\n{'='*80}",
            "REPOSITORY CONVERSION SUMMARY",
            f"{'='*80}",
            f"Repository Path: {self.repo_path}",
            f"Total Files Processed: {self.file_count}",
            f"Files Skipped: {len(self.skipped_files)}",
            f"Output File: {self.output_file}",
            f"Total Content Length: {len(''.join(self.text_content))} characters",
            f"{'='*80}\n"
        ]
        
        if self.skipped_files:
            summary.append("SKIPPED FILES:")
            summary.append("-" * 40)
            for file_path, error in self.skipped_files:
                summary.append(f"  {file_path}: {error}")
            summary.append("")
        
        return '\n'.join(summary)

    def convert(self) -> None:
        """Main conversion method."""
        print(f"Starting conversion of repository: {self.repo_path}")
        print(f"Output will be saved to: {self.output_file}")
        print("-" * 50)
        
        if not self.repo_path.exists():
            raise FileNotFoundError(f"Repository path does not exist: {self.repo_path}")
        
        # Add repository header
        self.text_content.append(f"LEAN-QUANTUMINFO REPOSITORY CONTENT")
        self.text_content.append(f"Repository: https://github.com/Timeroot/Lean-QuantumInfo.git")
        self.text_content.append(f"Generated on: {os.popen('date').read().strip()}")
        self.text_content.append(f"{'='*80}\n")
        
        # Process all files
        self.process_directory(self.repo_path)
        
        # Add summary
        self.text_content.append(self.generate_summary())
        
        # Write to output file
        try:
            with open(self.output_file, 'w', encoding='utf-8') as f:
                f.write('\n'.join(self.text_content))
            print(f"\nConversion completed successfully!")
            print(f"Output saved to: {self.output_file}")
            print(f"Total files processed: {self.file_count}")
        except Exception as e:
            print(f"Error writing output file: {e}")
            raise

def main():
    """Main function to run the converter."""
    # Default paths
    repo_path = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/Lean-QuantumInfo"
    output_file = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_full_content.txt"
    
    # Allow command line arguments
    if len(sys.argv) > 1:
        repo_path = sys.argv[1]
    if len(sys.argv) > 2:
        output_file = sys.argv[2]
    
    try:
        converter = RepoToTextConverter(repo_path, output_file)
        converter.convert()
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
