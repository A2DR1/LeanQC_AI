# Controlled Natural Language

## Introduction 

This project performs the following task:

NL -> CNL -> FL -> syntactic accuracy & semantic accuracy & overall accuracy

The key files are: 
- CNL_generation.py: Generate CNL from original NL. 
- cnl_rules.json: Contain rules for generating CNL. 
- FL_generation.py: Generate FL from NL and CNL. 
- lean_checker.py: Check syntactic accuray. 
- eval_semantic.py: Check semantic accuracy.
- pipeline.py: Performs everything and gets the accuracy. 

## Instructions

Please go over the key function and construct your own pipeline according to the data set given. 

## Potential Benchmarks 

1. miniF2F
2. ProofNet
3. PutnamBench
4. DeepMind Math
5. Fimo 
6. TheoremQA 