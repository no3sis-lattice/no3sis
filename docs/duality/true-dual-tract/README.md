# TRUE_DUAL_TRACT Formalization Chunks

## Structure
- chunks/chunk-NN-<slug>.md           # Natural language excerpt for chunk NN
- chunks/chunk-NN.constraints.json     # Structured constraints extracted (LLM output)
- chunks/chunk-NN.mzn                  # MiniZinc model (generated)
- chunks/chunk-NN.lean                 # Lean4 spec/proofs (generated)
- chunks/chunk-NN.notes.md             # Optional notes/logs

## Conventions
- NN: zero-padded index 01..71
- Slug: short dashed title from TRUE_DUAL_TRACT sections
- LLM only extracts constraints into JSON; logic/unification is handled by MiniZinc and Lean4
