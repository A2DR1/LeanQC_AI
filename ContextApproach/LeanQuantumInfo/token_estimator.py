#!/usr/bin/env python3
"""
Token Estimation Tool
Estimates token counts for text files using different tokenization methods.
"""

import re
import os
from pathlib import Path
from typing import Dict, List, Tuple

class TokenEstimator:
    def __init__(self):
        # Common token estimation methods
        self.methods = {
            'word_count': self.estimate_word_tokens,
            'character_count': self.estimate_character_tokens,
            'gpt_style': self.estimate_gpt_tokens,
            'tiktoken_style': self.estimate_tiktoken_tokens
        }
    
    def estimate_word_tokens(self, text: str) -> int:
        """Estimate tokens based on word count (rough approximation: 1 token ≈ 0.75 words)."""
        words = len(text.split())
        return int(words / 0.75)
    
    def estimate_character_tokens(self, text: str) -> int:
        """Estimate tokens based on character count (rough approximation: 1 token ≈ 4 characters)."""
        return int(len(text) / 4)
    
    def estimate_gpt_tokens(self, text: str) -> int:
        """More sophisticated GPT-style token estimation."""
        # Remove extra whitespace
        text = re.sub(r'\s+', ' ', text.strip())
        
        # Count words and punctuation
        words = len(text.split())
        
        # Count special characters and punctuation
        special_chars = len(re.findall(r'[^\w\s]', text))
        
        # Estimate: words + special chars + some overhead for encoding
        return int(words + special_chars * 0.5 + len(text) * 0.1)
    
    def estimate_tiktoken_tokens(self, text: str) -> int:
        """Estimate tokens using tiktoken-style approximation."""
        # This is a simplified version of tiktoken's BPE tokenization
        # In practice, tiktoken uses a more complex BPE algorithm
        
        # Count different types of tokens
        words = len(text.split())
        
        # Count code-specific tokens (common in Lean files)
        code_patterns = [
            r'\b\w+\s*:',  # variable declarations
            r'\b\w+\s*\(',  # function calls
            r'[{}()\[\]]',  # brackets
            r'[=<>!]+',     # operators
            r'[.,;]',       # punctuation
            r'/\*.*?\*/',   # comments
            r'--.*',         # line comments
        ]
        
        code_tokens = sum(len(re.findall(pattern, text)) for pattern in code_patterns)
        
        # Estimate total tokens
        return int(words * 1.3 + code_tokens * 0.8 + len(text) * 0.05)
    
    def estimate_tokens(self, text: str, method: str = 'gpt_style') -> int:
        """Estimate tokens using the specified method."""
        if method not in self.methods:
            raise ValueError(f"Unknown method: {method}. Available methods: {list(self.methods.keys())}")
        
        return self.methods[method](text)
    
    def analyze_file(self, file_path: str, methods: List[str] = None) -> Dict:
        """Analyze a single file and return token estimates."""
        if methods is None:
            methods = list(self.methods.keys())
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {'error': str(e)}
        
        file_stats = {
            'file_path': file_path,
            'file_size_bytes': os.path.getsize(file_path),
            'character_count': len(content),
            'line_count': len(content.splitlines()),
            'word_count': len(content.split()),
            'token_estimates': {}
        }
        
        for method in methods:
            try:
                tokens = self.estimate_tokens(content, method)
                file_stats['token_estimates'][method] = tokens
            except Exception as e:
                file_stats['token_estimates'][method] = f"Error: {e}"
        
        return file_stats
    
    def analyze_directory(self, directory: str, file_patterns: List[str] = None, methods: List[str] = None) -> List[Dict]:
        """Analyze all files in a directory."""
        if file_patterns is None:
            file_patterns = ['*.txt', '*.md', '*.lean', '*.py', '*.json']
        
        if methods is None:
            methods = list(self.methods.keys())
        
        directory = Path(directory)
        results = []
        
        for pattern in file_patterns:
            for file_path in directory.glob(pattern):
                if file_path.is_file():
                    result = self.analyze_file(str(file_path), methods)
                    results.append(result)
        
        return results
    
    def generate_report(self, analysis_results: List[Dict], output_file: str = None) -> str:
        """Generate a detailed report of token analysis."""
        report = []
        report.append("TOKEN ESTIMATION REPORT")
        report.append("=" * 50)
        report.append("")
        
        total_stats = {
            'total_files': len(analysis_results),
            'total_characters': 0,
            'total_words': 0,
            'total_tokens': {},
            'file_sizes': []
        }
        
        # Process each file
        for result in analysis_results:
            if 'error' in result:
                report.append(f"ERROR: {result['file_path']} - {result['error']}")
                continue
            
            report.append(f"File: {result['file_path']}")
            report.append(f"  Size: {result['file_size_bytes']:,} bytes")
            report.append(f"  Characters: {result['character_count']:,}")
            report.append(f"  Words: {result['word_count']:,}")
            report.append(f"  Lines: {result['line_count']:,}")
            
            report.append("  Token Estimates:")
            for method, tokens in result['token_estimates'].items():
                if isinstance(tokens, int):
                    report.append(f"    {method}: {tokens:,} tokens")
                    if method not in total_stats['total_tokens']:
                        total_stats['total_tokens'][method] = 0
                    total_stats['total_tokens'][method] += tokens
                else:
                    report.append(f"    {method}: {tokens}")
            
            report.append("")
            
            # Update totals
            total_stats['total_characters'] += result['character_count']
            total_stats['total_words'] += result['word_count']
            total_stats['file_sizes'].append(result['file_size_bytes'])
        
        # Add summary
        report.append("SUMMARY")
        report.append("-" * 30)
        report.append(f"Total files analyzed: {total_stats['total_files']}")
        report.append(f"Total characters: {total_stats['total_characters']:,}")
        report.append(f"Total words: {total_stats['total_words']:,}")
        report.append(f"Average file size: {sum(total_stats['file_sizes']) / len(total_stats['file_sizes']):,.0f} bytes")
        
        report.append("\nTotal Token Estimates:")
        for method, tokens in total_stats['total_tokens'].items():
            report.append(f"  {method}: {tokens:,} tokens")
        
        # Add model context limits for reference
        report.append("\nMODEL CONTEXT LIMITS (for reference):")
        model_limits = {
            'GPT-3.5-turbo': 4096,
            'GPT-4': 8192,
            'GPT-4-turbo': 128000,
            'GPT-4o': 128000,
            'Claude-3-Sonnet': 200000,
            'Claude-3-Opus': 200000,
            'Gemini-1.5-Pro': 2000000,
            'Gemini-1.5-Flash': 1000000
        }
        
        for model, limit in model_limits.items():
            report.append(f"  {model}: {limit:,} tokens")
            for method, tokens in total_stats['total_tokens'].items():
                if isinstance(tokens, int):
                    percentage = (tokens / limit) * 100
                    report.append(f"    - {method} estimate: {percentage:.1f}% of context limit")
        
        report_text = '\n'.join(report)
        
        if output_file:
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(report_text)
            print(f"Report saved to: {output_file}")
        
        return report_text

def main():
    """Main function to run token estimation."""
    estimator = TokenEstimator()
    
    # Analyze the generated text files
    files_to_analyze = [
        "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_full_content.txt",
        "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_simple.txt",
        "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_compact.txt",
        "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_prompt.txt"
    ]
    
    print("Analyzing token counts for generated files...")
    print("-" * 50)
    
    results = []
    for file_path in files_to_analyze:
        if os.path.exists(file_path):
            result = estimator.analyze_file(file_path)
            results.append(result)
        else:
            print(f"File not found: {file_path}")
    
    # Generate and display report
    report = estimator.generate_report(results, "token_analysis_report.txt")
    print(report)

if __name__ == "__main__":
    main()
