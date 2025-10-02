#!/usr/bin/env python3
"""
Create optimized system prompts for different AI models with different context limits.
"""

import os
from pathlib import Path

def create_optimized_system_prompts():
    """Create system prompts optimized for different AI models."""
    
    # Read the full repository content
    repo_file = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_full_content.txt"
    
    if not os.path.exists(repo_file):
        print(f"Repository file not found: {repo_file}")
        return
    
    with open(repo_file, 'r', encoding='utf-8') as f:
        repo_content = f.read()
    
    # Model configurations with context limits
    models = {
        'gpt-4': {'limit': 8000, 'description': 'GPT-4 (8K context)'},
        'gpt-4-turbo': {'limit': 128000, 'description': 'GPT-4 Turbo (128K context)'},
        'claude-3-sonnet': {'limit': 200000, 'description': 'Claude-3 Sonnet (200K context)'},
        'gemini-1.5-pro': {'limit': 2000000, 'description': 'Gemini-1.5 Pro (2M context)'}
    }
    
    # Base system prompt (without repository content)
    base_prompt = """# Lean 4 Code Generation System Prompt

You are an expert Lean 4 theorem prover specializing in quantum information theory. Convert natural language prompts into precise Lean 4 code using the Lean-QuantumInfo repository as reference.

## Your Role
Convert natural language descriptions of mathematical concepts, theorems, and proofs into formal Lean 4 code following the exact patterns, definitions, and conventions from the Lean-QuantumInfo repository.

## Key Repository Patterns

### Probability & Distributions
```lean
def Prob := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }
def Distribution (α : Type u) [Fintype α] : Type u :=
  { f : α → Prob // Finset.sum Finset.univ (fun i ↦ (f i : ℝ)) = 1 }
```

### Quantum States
```lean
structure MState (d : Type*) [Fintype d] :=
  m : Matrix d d ℂ
  pos : m.PosSemidef
  tr : m.trace = 1

structure Bra (d : ℕ) :=
  vec : Fin d → ℂ
  normalized' : ∑ i, ‖vec i‖^2 = 1
```

### Entropy Functions
```lean
def shannon_entropy (p : Distribution α) : ℝ :=
  -∑ x, (p.val x).toReal * Real.log (p.val x).toReal

def von_neumann_entropy (ρ : MState d) : ℝ :=
  -∑ i, (eigenvalues ρ.m i).toReal * Real.log (eigenvalues ρ.m i).toReal
```

### Channel Definitions
```lean
structure DMChannel where
  symb_dist : I → Distribution O

structure Code where
  encoder : List A → List I
  decoder : List O → List A
```

## Response Format
1. **Analysis**: Explain the mathematical concept
2. **Lean Code**: Complete implementation with imports
3. **Explanation**: Key components and mathematical meaning
4. **Dependencies**: Required imports and related definitions

## Guidelines
- Use Unicode: `ℝ`, `ℕ`, `ℂ`, `→`, `↔`, `∧`, `∨`, `∀`, `∃`
- Include docstrings: `/-- ... -/`
- Type annotations: `[Fintype α]`, `[DecidableEq α]`
- Use `sorry` for incomplete proofs
- Follow repository naming conventions
- Reference existing definitions when possible

Generate mathematically sound, well-documented Lean 4 code that accurately represents quantum information theory concepts.

## Repository Content Reference

The complete Lean-QuantumInfo repository content follows below. Use this as your comprehensive reference for all code generation:

---

"""
    
    # Create prompts for each model
    for model_name, config in models.items():
        print(f"Creating prompt for {config['description']}...")
        
        # Calculate how much repository content we can include
        base_size = len(base_prompt)
        available_space = config['limit'] - base_size - 1000  # Reserve 1000 tokens for response
        
        # Estimate tokens (rough approximation: 1 token ≈ 4 characters)
        available_chars = available_space * 4
        
        if available_chars >= len(repo_content):
            # Can include full repository
            prompt_content = base_prompt + repo_content
            print(f"  - Including full repository content ({len(repo_content):,} chars)")
        else:
            # Need to truncate repository content
            truncated_content = repo_content[:available_chars]
            # Try to end at a reasonable boundary (end of a file section)
            last_file_end = truncated_content.rfind('================================================================================')
            if last_file_end > available_chars * 0.8:  # If we can keep at least 80% of content
                truncated_content = truncated_content[:last_file_end]
                truncated_content += "\n\n[Repository content truncated due to context limits]"
            
            prompt_content = base_prompt + truncated_content
            print(f"  - Including truncated repository content ({len(truncated_content):,} chars)")
        
        # Write the prompt
        output_file = f"/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/system_prompt_{model_name}.txt"
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(prompt_content)
        
        print(f"  - Saved to: {output_file}")
        print(f"  - Total size: {len(prompt_content):,} characters")
        print()

def create_chunked_system_prompts():
    """Create system prompts that can be used in chunks."""
    
    # Read the full repository content
    repo_file = "/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/lean_quantum_info_full_content.txt"
    
    if not os.path.exists(repo_file):
        print(f"Repository file not found: {repo_file}")
        return
    
    with open(repo_file, 'r', encoding='utf-8') as f:
        repo_content = f.read()
    
    # Split repository content by files
    import re
    file_sections = re.split(r'(================================================================================\nFILE:.*?\n================================================================================)', repo_content)
    
    # Create a base prompt that can be used with chunks
    base_prompt = """# Lean 4 Code Generation System Prompt (Chunked Version)

You are an expert Lean 4 theorem prover specializing in quantum information theory. Convert natural language prompts into precise Lean 4 code using the Lean-QuantumInfo repository as reference.

## Your Role
Convert natural language descriptions of mathematical concepts, theorems, and proofs into formal Lean 4 code following the exact patterns, definitions, and conventions from the Lean-QuantumInfo repository.

## Key Repository Patterns

### Probability & Distributions
```lean
def Prob := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }
def Distribution (α : Type u) [Fintype α] : Type u :=
  { f : α → Prob // Finset.sum Finset.univ (fun i ↦ (f i : ℝ)) = 1 }
```

### Quantum States
```lean
structure MState (d : Type*) [Fintype d] :=
  m : Matrix d d ℂ
  pos : m.PosSemidef
  tr : m.trace = 1

structure Bra (d : ℕ) :=
  vec : Fin d → ℂ
  normalized' : ∑ i, ‖vec i‖^2 = 1
```

### Entropy Functions
```lean
def shannon_entropy (p : Distribution α) : ℝ :=
  -∑ x, (p.val x).toReal * Real.log (p.val x).toReal

def von_neumann_entropy (ρ : MState d) : ℝ :=
  -∑ i, (eigenvalues ρ.m i).toReal * Real.log (eigenvalues ρ.m i).toReal
```

## Response Format
1. **Analysis**: Explain the mathematical concept
2. **Lean Code**: Complete implementation with imports
3. **Explanation**: Key components and mathematical meaning
4. **Dependencies**: Required imports and related definitions

## Guidelines
- Use Unicode: `ℝ`, `ℕ`, `ℂ`, `→`, `↔`, `∧`, `∨`, `∀`, `∃`
- Include docstrings: `/-- ... -/`
- Type annotations: `[Fintype α]`, `[DecidableEq α]`
- Use `sorry` for incomplete proofs
- Follow repository naming conventions
- Reference existing definitions when possible

## Repository Content Reference

The following is a portion of the Lean-QuantumInfo repository content. Use this as reference for code generation:

---

"""
    
    # Create chunked prompts
    chunk_size = 50000  # characters per chunk
    chunk_num = 1
    
    for i in range(0, len(repo_content), chunk_size):
        chunk = repo_content[i:i + chunk_size]
        
        # Try to end at a reasonable boundary
        if i + chunk_size < len(repo_content):
            last_file_end = chunk.rfind('================================================================================')
            if last_file_end > chunk_size * 0.8:
                chunk = chunk[:last_file_end]
                chunk += "\n\n[Repository content continues in next chunk]"
        
        prompt_content = base_prompt + chunk
        
        output_file = f"/Users/austinshen/Documents/Umich/Research/LeanQC_AI/ContextApproach/LeanQuantumInfo/system_prompt_chunk_{chunk_num:02d}.txt"
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(prompt_content)
        
        print(f"Created chunk {chunk_num}: {output_file} ({len(prompt_content):,} chars)")
        chunk_num += 1

if __name__ == "__main__":
    print("Creating optimized system prompts for different models...")
    create_optimized_system_prompts()
    
    print("\nCreating chunked system prompts...")
    create_chunked_system_prompts()
    
    print("\nAll system prompts created successfully!")
