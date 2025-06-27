# Finiteness of Symbolic Derivatives in Lean

This repo contains the Lean formalization files for the paper "Finiteness of Symbolic Derivatives in Lean".

## Quick start
  1. Install VS Code and then install the `lean4` extension.
  2. Open this folder in VS Code.
  3. Open the `Finiteness.lean` file, which collects all modules of the formalization.

## Brief file overview
Listed below is a brief description of each file of the formalization.

- `Evaluation` : contains the definition of the `evaluation` function for concrete locations. Here, we prove that symbolic derivatives preserve match semantics. 
- `Finite` : contains the main finiteness result.
- `NeSublists` : contains definitions and lemmas about non-empty sublists.
- `Permute` : contains definitions and lemmas about the key functions `sum`, `neSubsets`, and `sumSubsets`.
- `Pieces` : contains the definitions and lemmas about `pieces` and also `piecesS` (`pieces` as a closure operator).
- `Similarity` : contains the definition of the similarity relation.
- `Simplifications` : contains admissible simplifications which preserve the finiteness result.
- `StepsNotIdem` : contains the proof that the `step` function is not idempotent. 
- `SubsetUptTo` : contains definitions and lemmas about reasoning up-to i.e. the functions  `mem_up_to`, `subset_up_to` and `equality_up_to`.
- `SymbolicDerivative`: contains the definitions of symbolic derivatives and the `step` function.
- `TTerm` : main definitions and lemmas about transition terms.