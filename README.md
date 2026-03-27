# LeanQC_AI

**LeanQC_AI** is a research project exploring AI-driven *autoformalization* — automatically translating natural language mathematical and quantum computing statements into verified formal proofs written in [Lean 4](https://leanprover.github.io/). The project combines a hand-crafted quantum computing library with multiple LLM-based approaches for generating, evaluating, and improving formal theorem statements.

---

## 📋 Table of Contents

- [Overview](#overview)
- [Project Structure](#project-structure)
- [Components](#components)
  - [LeanQC – Quantum Computing Library](#leanqc--quantum-computing-library)
  - [ControlledNaturalLanguage – CNL Pipeline](#controllednaturallanguage--cnl-pipeline)
  - [ContextApproach – Prompt Engineering](#contextapproach--prompt-engineering)
  - [RAGApproach – Retrieval-Augmented Generation](#ragapproach--retrieval-augmented-generation)
  - [AutoEvaluation – Automated Lean Verification](#autoevaluation--automated-lean-verification)
  - [papers/Mathesis – Mathesis Paper Replication](#papersmathesis--mathesis-paper-replication)
- [Experimental Results](#experimental-results)
- [Getting Started](#getting-started)
- [Requirements](#requirements)

---

## Overview

Formal verification of mathematics is a growing field, but writing proofs in interactive theorem provers like Lean 4 requires significant expert knowledge. This project investigates how large language models (LLMs) can bridge the gap between informal mathematical language and verified Lean 4 code, with a particular focus on quantum computing theorems.

The three main research directions explored are:

1. **Controlled Natural Language (CNL):** Transform informal statements into a structured intermediate language before autoformalization, hypothesizing that a constrained vocabulary reduces LLM errors.
2. **Context Window Approach:** Supply LLMs with rich contextual prompts drawn from the repository and reference datasets (Gaokao, Mathesis, LeanQuantumInfo) to improve output quality.
3. **Retrieval-Augmented Generation (RAG):** Use a vector database built from the LeanQC library to let the LLM retrieve relevant definitions and examples at query time.

---

## Project Structure

```
LeanQC_AI/
├── LeanQC/                        # Core Lean 4 quantum computing library
│   ├── Leanqc/
│   │   ├── Basic/
│   │   │   ├── Qudit.lean         # Qudit/qubit definitions, No-Cloning theorem
│   │   │   └── Pauli.lean         # Pauli X/Y/Z matrices and properties
│   │   └── Util/Math.lean         # Mathematical utilities (Kronecker, etc.)
│   ├── TextBookExercise/          # Lean proofs of textbook exercises (Ch1–Ch5)
│   ├── lakefile.lean              # Lake build configuration
│   └── lean-toolchain             # Lean version pin
│
├── ControlledNaturalLanguage/     # NL → CNL → FL pipeline
│   ├── CNL_generation.py          # Generate CNL from informal statements via LLM
│   ├── FL_generation.py           # Translate CNL to Lean 4 formal language
│   ├── lean_checker.py            # Syntactic correctness check
│   ├── eval_semantic.py           # Semantic equivalence evaluation
│   ├── pipeline.py                # End-to-end pipeline runner
│   ├── cnl_rules.json             # Versioned CNL grammar rules (v1–v7)
│   └── history/                   # Experiment outputs (CNL statements, Lean files, NL-FL pairs)
│
├── ContextApproach/               # Prompt engineering and context window experiments
│   ├── LeanQuantumInfo/           # System prompts built from the LeanQuantumInfo repo
│   └── Gaokao/                    # Experiments on the Gaokao-Formal dataset
│
├── RAGApproach/                   # Retrieval-Augmented Generation pipeline
│   ├── setup.py                   # RAG chain setup (LangChain + FAISS)
│   ├── repo.txt                   # LeanQC repo converted to plain text for embedding
│   └── theoremlist.json           # Curated list of quantum computing theorem statements
│
├── AutoEvaluation/                # Automated Lean verification framework
│   ├── tools/
│   │   ├── EvalScript.py          # Batch compile and report errors
│   │   └── EvalScript_byTheorem.py# Per-theorem error mapping
│   ├── Generated/                 # LLM-generated Lean files (CNL v1–v4, miniF2F)
│   ├── lean_syntax_checker.py     # Lean syntax checker utility
│   ├── lean_server.py             # Lean language server integration
│   └── lakefile.toml              # Lake build config for evaluation workspace
│
├── papers/Mathesis/               # Replication of the Mathesis autoformalization paper
│   ├── Mathesis.ipynb             # Notebook with prompt experiments
│   ├── Mathesis_tests.py          # Test scripts
│   └── prompts.txt                # Prompt templates used
│
├── Fundamentals of Quantum Computing.ipynb  # Educational quantum computing notebook
├── Python_LLM_Test.ipynb          # Notebook for direct LLM capability testing
├── lean-tactics.pdf               # Lean tactic reference (PDF)
└── requirement.txt                # Python package dependencies
```

---

## Components

### LeanQC – Quantum Computing Library

A hand-crafted Lean 4 library providing formal definitions and theorems for quantum computing primitives. It depends on [Mathlib](https://github.com/leanprover-community/mathlib4) and optionally on [LeanCopilot](https://github.com/lean-dojo/LeanCopilot) and [Paperproof](https://github.com/Paper-Proof/paperproof).

**Key definitions and theorems:**

| File | Content |
|------|---------|
| `Leanqc/Basic/Qudit.lean` | `Qudit` (pure quantum state), `Qubit`, `QubitZero`/`QubitOne`, `UnitaryOp`, `ApplyUnitaryOp`, inner product, `noCloning` (No-Cloning theorem proof) |
| `Leanqc/Basic/Pauli.lean` | Pauli X, Y, Z matrices; Hermitian proof for Pauli X |
| `Leanqc/Util/Math.lean` | Kronecker product utilities, `flatten_kronecker` |
| `TextBookExercise/Chapter*.lean` | Formal Lean 4 exercises from a quantum computing textbook |

The **No-Cloning theorem** is fully proved in Lean 4:
```lean
theorem noCloning :
    ¬∃ (U : UnitaryOp 4), ∀ ψ : Qubit,
        ApplyUnitaryOp U (compose_qudits ψ Qubit.Zero) = compose_qudits ψ ψ
```

---

### ControlledNaturalLanguage – CNL Pipeline

This component tests whether inserting a *Controlled Natural Language* (CNL) intermediate step improves LLM autoformalization accuracy. The hypothesis is that a more structured, restricted language reduces the ambiguity that LLMs face when targeting Lean 4 syntax.

**Pipeline:**
```
Informal NL statement
        ↓  (CNL_generation.py — DeepSeek API)
Controlled Natural Language (CNL)
        ↓  (FL_generation.py — DeepSeek API)
Lean 4 formal theorem statement
        ↓  (lean_checker.py + eval_semantic.py)
Syntactic accuracy  +  Semantic accuracy
```

Seven versions of CNL rules (`cnl_rules.json`, v1–v7) were designed and tested on the [miniF2F](https://github.com/openai/miniF2F) benchmark (100 informal test statements).

---

### ContextApproach – Prompt Engineering

Investigates the effect of providing LLMs with rich context (the full LeanQC repository, reference datasets, or prompt templates based on published papers) on autoformalization quality.

**Subdirectories:**

- **`LeanQuantumInfo/`** – Tools to convert the [Lean-QuantumInfo](https://github.com/) repository into prompt-friendly text. Includes token analysis, chunking scripts, and system prompts tailored for GPT-4, GPT-4-Turbo, Claude 3 Sonnet, and Gemini 1.5/2.5 Pro.
- **`Gaokao/`** – Experiments on 50 problems from the [Gaokao-Formal v3](https://github.com/Huawei-AI4Math/Mathesis/blob/main/Gaokao-Formal_v3.json) dataset using Mathesis-style and ATLAS-style prompt templates.

**Supported LLM context windows:**

| Model | Context Window |
|-------|---------------|
| GPT-4o | 128,000 tokens |
| Claude 3 Sonnet | 200,000 tokens |
| Gemini 1.5 Pro | 2,000,000 tokens |
| Gemini 2.5 Pro | 1,000,000 – 2,000,000 tokens |
| Goedel Prover | ~16,000 tokens |

---

### RAGApproach – Retrieval-Augmented Generation

Uses [LangChain](https://python.langchain.com/) and [FAISS](https://github.com/facebookresearch/faiss) to build a retrieval system over the LeanQC codebase. At query time the system fetches relevant definitions and lemmas before generating a Lean 4 formalization.

**Supports:**
- **OpenAI** models (GPT-4) via `langchain-openai`
- **Local Ollama** models (Llama 2) via `langchain-ollama`

**Usage:**
```bash
cd RAGApproach
python setup.py
```

---

### AutoEvaluation – Automated Lean Verification

A Python framework that batch-compiles LLM-generated Lean files and maps compilation errors back to individual theorem names, enabling per-theorem accuracy metrics.

**Key scripts:**

| Script | Purpose |
|--------|---------|
| `tools/EvalScript_byTheorem.py` | Run `lake env lean` on every `.lean` file in `Generated/`, extract errors, map each error to its theorem name, print summary |
| `lean_syntax_checker.py` | Lightweight syntax check without full compilation |
| `lean_server.py` | Uses the Lean language server protocol for interactive checking |

**Generated files evaluated:**
- `CNL_v1` through `CNL_v4` — outputs of the CNL pipeline for different rule versions
- `miniF2F_plain` — direct (no CNL) autoformalization baseline

---

### papers/Mathesis – Mathesis Paper Replication

Contains experiments replicating and extending the [Mathesis](https://arxiv.org/abs/2403.09517) paper (*Towards Formal Theorem Proving from Natural Languages*). Includes Jupyter notebooks, prompt templates, and evaluation results.

---

## Experimental Results

The CNL pipeline was evaluated over 7 independent trials on 100 miniF2F test problems. Below are representative results (Trial 1):

| Variant | Syntactic Accuracy | Semantic Accuracy |
|---------|-------------------|------------------|
| miniF2F (no CNL) | 70% | 24% |
| CNL v1 | 70% | 24% |
| CNL v2 | 65% | 38% |
| CNL v3 | 71% | 27% |
| CNL v4 | 72% | 33% |
| CNL v5 | 65% | 38% |
| CNL v6 | 66% | 30% |
| **CNL v7** | **57%** | **49%** |

**Key finding:** Later CNL versions (v7) trade syntactic correctness for significantly higher semantic accuracy, suggesting that a more constrained intermediate language helps LLMs capture meaning even when the output Lean syntax requires post-processing.

---

## Getting Started

### 1. Lean 4 Library (LeanQC)

```bash
# Prerequisites: elan (Lean version manager) and Lake
git clone https://github.com/A2DR1/LeanQC_AI.git
cd LeanQC_AI/LeanQC
lake update
lake build
```

### 2. Python Pipelines

```bash
pip install -r requirement.txt
```

Set your API keys in a `.env` file:
```
OPENAI_API_KEY=sk-...
DEEPSEEK_API_KEY=sk-...
```

**Run the CNL pipeline:**
```bash
cd ControlledNaturalLanguage
python pipeline.py  # prompts for version number (1–7)
```

**Run AutoEvaluation:**
```bash
cd AutoEvaluation
lake update && lake build
python tools/EvalScript_byTheorem.py
```

**Run the RAG pipeline:**
```bash
cd RAGApproach
python setup.py
```

---

## Requirements

- **Lean 4** ≥ 4.22.0 (via [elan](https://github.com/leanprover/elan))
- **Lake** (bundled with elan)
- **Python** 3.9+
- See `requirement.txt` for all Python dependencies (LangChain, FAISS, OpenAI, ChromaDB, etc.) 