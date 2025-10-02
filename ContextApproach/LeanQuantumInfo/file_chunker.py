#!/usr/bin/env python3
"""
File Chunker Utility
Splits large text files into smaller chunks suitable for different AI models.
"""

import os
import re
from pathlib import Path
from typing import List, Dict, Optional
from advanced_token_analyzer import AdvancedTokenAnalyzer

class FileChunker:
    def __init__(self):
        self.analyzer = AdvancedTokenAnalyzer()
    
    def chunk_by_file_sections(self, file_path: str, model: str = 'gpt-4', output_dir: str = None) -> List[Dict]:
        """Split file by individual file sections (best for repository content)."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return [{'error': str(e)}]
        
        if output_dir is None:
            output_dir = os.path.join(os.path.dirname(file_path), 'chunks')
        
        os.makedirs(output_dir, exist_ok=True)
        
        # Split by file sections
        sections = re.split(r'(## File:.*?\n)', content)
        
        chunks = []
        current_chunk = ""
        current_chunk_tokens = 0
        chunk_num = 1
        file_sections_in_chunk = 0
        
        model_config = self.analyzer.model_configs[model]
        max_tokens = model_config['context_limit'] - 1000  # Reserve space for context
        
        for i, section in enumerate(sections):
            if not section.strip():
                continue
            
            section_tokens = self.analyzer.estimate_tokens_accurate(section, model)
            
            # Check if adding this section would exceed the limit
            if current_chunk_tokens + section_tokens > max_tokens and current_chunk:
                # Save current chunk
                chunk_filename = f"chunk_{chunk_num:03d}_{model}.txt"
                chunk_path = os.path.join(output_dir, chunk_filename)
                
                with open(chunk_path, 'w', encoding='utf-8') as f:
                    f.write(current_chunk.strip())
                
                chunks.append({
                    'chunk_number': chunk_num,
                    'filename': chunk_filename,
                    'path': chunk_path,
                    'tokens': current_chunk_tokens,
                    'file_sections': file_sections_in_chunk,
                    'size_bytes': os.path.getsize(chunk_path)
                })
                
                chunk_num += 1
                current_chunk = section
                current_chunk_tokens = section_tokens
                file_sections_in_chunk = 1 if section.startswith('## File:') else 0
            else:
                current_chunk += section
                current_chunk_tokens += section_tokens
                if section.startswith('## File:'):
                    file_sections_in_chunk += 1
        
        # Add final chunk
        if current_chunk.strip():
            chunk_filename = f"chunk_{chunk_num:03d}_{model}.txt"
            chunk_path = os.path.join(output_dir, chunk_filename)
            
            with open(chunk_path, 'w', encoding='utf-8') as f:
                f.write(current_chunk.strip())
            
            chunks.append({
                'chunk_number': chunk_num,
                'filename': chunk_filename,
                'path': chunk_path,
                'tokens': current_chunk_tokens,
                'file_sections': file_sections_in_chunk,
                'size_bytes': os.path.getsize(chunk_path)
            })
        
        return chunks
    
    def chunk_by_lines(self, file_path: str, model: str = 'gpt-4', output_dir: str = None) -> List[Dict]:
        """Split file by lines."""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return [{'error': str(e)}]
        
        if output_dir is None:
            output_dir = os.path.join(os.path.dirname(file_path), 'chunks')
        
        os.makedirs(output_dir, exist_ok=True)
        
        lines = content.splitlines()
        total_tokens = self.analyzer.estimate_tokens_accurate(content, model)
        model_config = self.analyzer.model_configs[model]
        max_tokens = model_config['context_limit'] - 1000
        
        lines_per_chunk = int((max_tokens * len(lines)) / total_tokens)
        
        chunks = []
        for i in range(0, len(lines), lines_per_chunk):
            chunk_lines = lines[i:i + lines_per_chunk]
            chunk_content = '\n'.join(chunk_lines)
            chunk_tokens = self.analyzer.estimate_tokens_accurate(chunk_content, model)
            
            chunk_num = len(chunks) + 1
            chunk_filename = f"chunk_{chunk_num:03d}_{model}.txt"
            chunk_path = os.path.join(output_dir, chunk_filename)
            
            with open(chunk_path, 'w', encoding='utf-8') as f:
                f.write(chunk_content)
            
            chunks.append({
                'chunk_number': chunk_num,
                'filename': chunk_filename,
                'path': chunk_path,
                'tokens': chunk_tokens,
                'line_range': f"{i+1}-{min(i+lines_per_chunk, len(lines))}",
                'lines': len(chunk_lines),
                'size_bytes': os.path.getsize(chunk_path)
            })
        
        return chunks
    
    def create_chunk_index(self, chunks: List[Dict], output_file: str) -> None:
        """Create an index file listing all chunks."""
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write("CHUNK INDEX\n")
            f.write("=" * 50 + "\n\n")
            
            total_tokens = sum(chunk.get('tokens', 0) for chunk in chunks if 'tokens' in chunk)
            total_files = sum(chunk.get('file_sections', 0) for chunk in chunks if 'file_sections' in chunk)
            
            f.write(f"Total chunks: {len(chunks)}\n")
            f.write(f"Total tokens: {total_tokens:,}\n")
            if total_files > 0:
                f.write(f"Total file sections: {total_files}\n")
            f.write("\n")
            
            for chunk in chunks:
                if 'error' in chunk:
                    f.write(f"ERROR: {chunk['error']}\n")
                    continue
                
                f.write(f"Chunk {chunk['chunk_number']:03d}: {chunk['filename']}\n")
                f.write(f"  Tokens: {chunk.get('tokens', 0):,}\n")
                f.write(f"  Size: {chunk.get('size_bytes', 0):,} bytes\n")
                
                if 'file_sections' in chunk:
                    f.write(f"  File sections: {chunk['file_sections']}\n")
                if 'line_range' in chunk:
                    f.write(f"  Lines: {chunk['line_range']}\n")
                if 'lines' in chunk:
                    f.write(f"  Line count: {chunk['lines']}\n")
                
                f.write(f"  Path: {chunk['path']}\n\n")
    
    def chunk_file(self, file_path: str, model: str = 'gpt-4', method: str = 'by_file_sections', output_dir: str = None) -> Dict:
        """Main function to chunk a file."""
        if not os.path.exists(file_path):
            return {'error': f"File not found: {file_path}"}
        
        if output_dir is None:
            output_dir = os.path.join(os.path.dirname(file_path), f'chunks_{model}')
        
        print(f"Chunking {os.path.basename(file_path)} for {model}...")
        print(f"Method: {method}")
        print(f"Output directory: {output_dir}")
        print("-" * 50)
        
        # Choose chunking method
        if method == 'by_file_sections':
            chunks = self.chunk_by_file_sections(file_path, model, output_dir)
        elif method == 'by_lines':
            chunks = self.chunk_by_file_sections(file_path, model, output_dir)
        else:
            return {'error': f"Unknown chunking method: {method}"}
        
        if chunks and 'error' in chunks[0]:
            return chunks[0]
        
        # Create index file
        index_file = os.path.join(output_dir, 'chunk_index.txt')
        self.create_chunk_index(chunks, index_file)
        
        # Print summary
        print(f"Created {len(chunks)} chunks")
        print(f"Index file: {index_file}")
        
        for chunk in chunks:
            if 'error' not in chunk:
                print(f"  {chunk['filename']}: {chunk['tokens']:,} tokens")
        
        return {
            'success': True,
            'chunks': chunks,
            'output_dir': output_dir,
            'index_file': index_file,
            'total_chunks': len(chunks),
            'total_tokens': sum(chunk.get('tokens', 0) for chunk in chunks if 'tokens' in chunk)
        }

def main():
    """Main function to demonstrate chunking."""
    chunker = FileChunker()
    
    # Files to chunk
    files_to_chunk = [
        "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_simple.txt",
        "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_full_content.txt"
    ]
    
    # Models to create chunks for
    models = ['gpt-4', 'gpt-4-turbo', 'claude-3-sonnet']
    
    for file_path in files_to_chunk:
        if os.path.exists(file_path):
            print(f"\n{'='*60}")
            print(f"CHUNKING: {os.path.basename(file_path)}")
            print(f"{'='*60}")
            
            for model in models:
                print(f"\nCreating chunks for {model}...")
                result = chunker.chunk_file(file_path, model, 'by_file_sections')
                
                if 'error' in result:
                    print(f"Error: {result['error']}")
                else:
                    print(f"Success! Created {result['total_chunks']} chunks")
                    print(f"Total tokens: {result['total_tokens']:,}")
        else:
            print(f"File not found: {file_path}")

if __name__ == "__main__":
    main()
