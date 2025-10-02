#!/usr/bin/env python3
"""
Advanced Token Analyzer
Provides detailed token analysis with chunking recommendations for large files.
"""

import re
import os
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import json

class AdvancedTokenAnalyzer:
    def __init__(self):
        # More accurate token estimation based on different models
        self.model_configs = {
            'gpt-3.5-turbo': {'context_limit': 4096, 'tokens_per_char': 0.25},
            'gpt-4': {'context_limit': 8192, 'tokens_per_char': 0.25},
            'gpt-4-turbo': {'context_limit': 128000, 'tokens_per_char': 0.25},
            'gpt-4o': {'context_limit': 128000, 'tokens_per_char': 0.25},
            'claude-3-sonnet': {'context_limit': 200000, 'tokens_per_char': 0.3},
            'claude-3-opus': {'context_limit': 200000, 'tokens_per_char': 0.3},
            'gemini-1.5-pro': {'context_limit': 2000000, 'tokens_per_char': 0.2},
            'gemini-1.5-flash': {'context_limit': 1000000, 'tokens_per_char': 0.2}
        }
    
    def estimate_tokens_accurate(self, text: str, model: str = 'gpt-4') -> int:
        """More accurate token estimation based on model-specific characteristics."""
        if model not in self.model_configs:
            model = 'gpt-4'  # fallback
        
        config = self.model_configs[model]
        
        # Clean text
        text = re.sub(r'\s+', ' ', text.strip())
        
        # Count different types of content
        words = len(text.split())
        characters = len(text)
        
        # Count code-specific patterns (important for Lean files)
        code_patterns = {
            'keywords': len(re.findall(r'\b(def|theorem|lemma|structure|class|instance|variable|open|import|namespace|end|sorry|have|show|by|exact|apply|rw|simp|unfold|cases|induction|constructor|intro|exists|forall|∃|∀|→|↔|∧|∨|¬|≠|≤|≥|<|>|=|∈|∉|⊆|⊂|∪|∩|∅|ℝ|ℕ|ℤ|ℚ|ℂ|Type|Prop|Sort)\b', text)),
            'operators': len(re.findall(r'[+\-*/=<>!&|^~%]+', text)),
            'brackets': len(re.findall(r'[{}()\[\]]', text)),
            'punctuation': len(re.findall(r'[.,;:]', text)),
            'comments': len(re.findall(r'--.*|/\*.*?\*/', text, re.DOTALL)),
            'strings': len(re.findall(r'"[^"]*"', text)),
            'numbers': len(re.findall(r'\b\d+\.?\d*\b', text))
        }
        
        # Calculate token estimate
        base_tokens = words * 1.3  # Base word tokens
        code_tokens = sum(code_patterns.values()) * 0.7  # Code-specific tokens
        char_tokens = characters * config['tokens_per_char']  # Character-based estimate
        
        # Use the more conservative estimate
        return int(max(base_tokens + code_tokens, char_tokens))
    
    def analyze_file_detailed(self, file_path: str) -> Dict:
        """Perform detailed analysis of a single file."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return {'error': str(e)}
        
        file_stats = {
            'file_path': file_path,
            'file_name': os.path.basename(file_path),
            'file_size_bytes': os.path.getsize(file_path),
            'character_count': len(content),
            'line_count': len(content.splitlines()),
            'word_count': len(content.split()),
            'non_empty_lines': len([line for line in content.splitlines() if line.strip()]),
            'token_estimates': {},
            'chunking_recommendations': {}
        }
        
        # Estimate tokens for different models
        for model in self.model_configs.keys():
            tokens = self.estimate_tokens_accurate(content, model)
            file_stats['token_estimates'][model] = tokens
            
            # Calculate if file fits in context
            context_limit = self.model_configs[model]['context_limit']
            fits_in_context = tokens <= context_limit
            percentage = (tokens / context_limit) * 100
            
            file_stats['chunking_recommendations'][model] = {
                'tokens': tokens,
                'context_limit': context_limit,
                'fits_in_context': fits_in_context,
                'percentage_of_limit': round(percentage, 1),
                'needs_chunking': not fits_in_context,
                'recommended_chunk_size': min(tokens, context_limit - 1000) if not fits_in_context else tokens
            }
        
        return file_stats
    
    def suggest_chunking_strategy(self, file_path: str, model: str = 'gpt-4') -> Dict:
        """Suggest how to chunk a large file for a specific model."""
        analysis = self.analyze_file_detailed(file_path)
        
        if 'error' in analysis:
            return analysis
        
        model_config = self.model_configs[model]
        tokens = analysis['token_estimates'][model]
        context_limit = model_config['context_limit']
        
        if tokens <= context_limit:
            return {
                'needs_chunking': False,
                'message': f"File fits within {model} context limit ({tokens:,} / {context_limit:,} tokens)"
            }
        
        # Suggest chunking strategies
        strategies = []
        
        # Strategy 1: By file sections (if it's a multi-file content)
        if '## File:' in analysis.get('content', ''):
            file_sections = re.split(r'## File:.*?\n', analysis.get('content', ''))
            strategies.append({
                'method': 'by_file_sections',
                'description': 'Split by individual files in the repository',
                'estimated_chunks': len([s for s in file_sections if s.strip()]),
                'avg_tokens_per_chunk': tokens // len([s for s in file_sections if s.strip()])
            })
        
        # Strategy 2: By lines
        lines = analysis['line_count']
        lines_per_chunk = int((context_limit - 1000) * lines / tokens)  # Reserve 1000 tokens for context
        strategies.append({
            'method': 'by_lines',
            'description': f'Split into chunks of ~{lines_per_chunk} lines each',
            'estimated_chunks': (lines + lines_per_chunk - 1) // lines_per_chunk,
            'lines_per_chunk': lines_per_chunk
        })
        
        # Strategy 3: By character count
        chars_per_chunk = int((context_limit - 1000) * analysis['character_count'] / tokens)
        strategies.append({
            'method': 'by_characters',
            'description': f'Split into chunks of ~{chars_per_chunk:,} characters each',
            'estimated_chunks': (analysis['character_count'] + chars_per_chunk - 1) // chars_per_chunk,
            'chars_per_chunk': chars_per_chunk
        })
        
        return {
            'needs_chunking': True,
            'total_tokens': tokens,
            'context_limit': context_limit,
            'excess_tokens': tokens - context_limit,
            'strategies': strategies,
            'recommended_strategy': strategies[0]  # Default to first strategy
        }
    
    def create_chunks(self, file_path: str, model: str = 'gpt-4', chunk_method: str = 'by_file_sections') -> List[Dict]:
        """Create actual chunks of the file for the specified model."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return [{'error': str(e)}]
        
        model_config = self.model_configs[model]
        context_limit = model_config['context_limit']
        max_chunk_tokens = context_limit - 1000  # Reserve space for context
        
        chunks = []
        
        if chunk_method == 'by_file_sections' and '## File:' in content:
            # Split by file sections
            sections = re.split(r'(## File:.*?\n)', content)
            current_chunk = ""
            current_chunk_tokens = 0
            chunk_num = 1
            
            for section in sections:
                if not section.strip():
                    continue
                
                section_tokens = self.estimate_tokens_accurate(section, model)
                
                if current_chunk_tokens + section_tokens > max_chunk_tokens and current_chunk:
                    # Save current chunk
                    chunks.append({
                        'chunk_number': chunk_num,
                        'tokens': current_chunk_tokens,
                        'content': current_chunk.strip(),
                        'file_sections': len(re.findall(r'## File:', current_chunk))
                    })
                    chunk_num += 1
                    current_chunk = section
                    current_chunk_tokens = section_tokens
                else:
                    current_chunk += section
                    current_chunk_tokens += section_tokens
            
            # Add final chunk
            if current_chunk.strip():
                chunks.append({
                    'chunk_number': chunk_num,
                    'tokens': current_chunk_tokens,
                    'content': current_chunk.strip(),
                    'file_sections': len(re.findall(r'## File:', current_chunk))
                })
        
        elif chunk_method == 'by_lines':
            # Split by lines
            lines = content.splitlines()
            lines_per_chunk = int(max_chunk_tokens * len(lines) / self.estimate_tokens_accurate(content, model))
            
            for i in range(0, len(lines), lines_per_chunk):
                chunk_lines = lines[i:i + lines_per_chunk]
                chunk_content = '\n'.join(chunk_lines)
                chunk_tokens = self.estimate_tokens_accurate(chunk_content, model)
                
                chunks.append({
                    'chunk_number': len(chunks) + 1,
                    'tokens': chunk_tokens,
                    'content': chunk_content,
                    'line_range': f"{i+1}-{min(i+lines_per_chunk, len(lines))}"
                })
        
        return chunks
    
    def generate_analysis_report(self, file_path: str, output_file: str = None) -> str:
        """Generate a comprehensive analysis report."""
        analysis = self.analyze_file_detailed(file_path)
        
        if 'error' in analysis:
            return f"Error analyzing file: {analysis['error']}"
        
        report = []
        report.append("ADVANCED TOKEN ANALYSIS REPORT")
        report.append("=" * 50)
        report.append(f"File: {analysis['file_name']}")
        report.append(f"Path: {analysis['file_path']}")
        report.append("")
        
        # Basic stats
        report.append("FILE STATISTICS:")
        report.append(f"  Size: {analysis['file_size_bytes']:,} bytes")
        report.append(f"  Characters: {analysis['character_count']:,}")
        report.append(f"  Words: {analysis['word_count']:,}")
        report.append(f"  Lines: {analysis['line_count']:,}")
        report.append(f"  Non-empty lines: {analysis['non_empty_lines']:,}")
        report.append("")
        
        # Token estimates
        report.append("TOKEN ESTIMATES BY MODEL:")
        for model, tokens in analysis['token_estimates'].items():
            config = self.model_configs[model]
            percentage = (tokens / config['context_limit']) * 100
            status = "✓ FITS" if tokens <= config['context_limit'] else "✗ TOO LARGE"
            report.append(f"  {model:20}: {tokens:8,} tokens ({percentage:5.1f}% of limit) {status}")
        report.append("")
        
        # Chunking recommendations
        report.append("CHUNKING RECOMMENDATIONS:")
        for model in self.model_configs.keys():
            rec = analysis['chunking_recommendations'][model]
            if rec['needs_chunking']:
                report.append(f"  {model}: Needs chunking ({rec['tokens']:,} tokens > {rec['context_limit']:,} limit)")
                report.append(f"    Recommended chunk size: {rec['recommended_chunk_size']:,} tokens")
            else:
                report.append(f"  {model}: No chunking needed")
        report.append("")
        
        # Detailed chunking strategy for the largest model that needs it
        models_needing_chunking = [m for m, rec in analysis['chunking_recommendations'].items() if rec['needs_chunking']]
        if models_needing_chunking:
            # Use the model with the smallest context limit that still needs chunking
            smallest_model = min(models_needing_chunking, key=lambda m: self.model_configs[m]['context_limit'])
            strategy = self.suggest_chunking_strategy(file_path, smallest_model)
            
            report.append(f"DETAILED CHUNKING STRATEGY FOR {smallest_model.upper()}:")
            report.append(f"  Total tokens: {strategy['total_tokens']:,}")
            report.append(f"  Context limit: {strategy['context_limit']:,}")
            report.append(f"  Excess tokens: {strategy['excess_tokens']:,}")
            report.append("")
            
            report.append("  Available strategies:")
            for i, strat in enumerate(strategy['strategies'], 1):
                report.append(f"    {i}. {strat['description']}")
                report.append(f"       Estimated chunks: {strat['estimated_chunks']}")
                if 'avg_tokens_per_chunk' in strat:
                    report.append(f"       Avg tokens per chunk: {strat['avg_tokens_per_chunk']:,}")
                if 'lines_per_chunk' in strat:
                    report.append(f"       Lines per chunk: {strat['lines_per_chunk']:,}")
                if 'chars_per_chunk' in strat:
                    report.append(f"       Characters per chunk: {strat['chars_per_chunk']:,}")
                report.append("")
        
        report_text = '\n'.join(report)
        
        if output_file:
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(report_text)
            print(f"Analysis report saved to: {output_file}")
        
        return report_text

def main():
    """Main function to run advanced token analysis."""
    analyzer = AdvancedTokenAnalyzer()
    
    # Analyze the main files
    files_to_analyze = [
        "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_simple.txt",
        "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_full_content.txt"
    ]
    
    for file_path in files_to_analyze:
        if os.path.exists(file_path):
            print(f"\nAnalyzing: {os.path.basename(file_path)}")
            print("-" * 50)
            
            # Generate detailed report
            report = analyzer.generate_analysis_report(file_path, f"advanced_analysis_{os.path.basename(file_path)}.txt")
            print(report)
            
            # Show chunking strategy
            strategy = analyzer.suggest_chunking_strategy(file_path, 'gpt-4')
            if strategy.get('needs_chunking'):
                print(f"\nChunking needed for GPT-4:")
                print(f"  Total tokens: {strategy['total_tokens']:,}")
                print(f"  Context limit: {strategy['context_limit']:,}")
                print(f"  Recommended strategy: {strategy['recommended_strategy']['description']}")
        else:
            print(f"File not found: {file_path}")

if __name__ == "__main__":
    main()
