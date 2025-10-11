# Duality Formalization

Divide-and-conquer formalization for TRUE_DUAL_TRACT using the Formal Triad:
- LLM (extraction only): produce per-chunk constraints JSON.
- MiniZinc: constraint modeling/optimization (8D unit-sum space, Monster primes, Gödelization).
- Lean 4: propositions and proofs mirroring the constraints.

## Structure
- index.md — progress and checklist
- templates/ — chunk templates (constraints, MiniZinc, Lean)
- scripts/ — render tools (constraints JSON → .mzn, .lean)
- true-dual-tract/ — chunks and artifacts

## Workflow
1) Extract constraints to chunk-NN.constraints.json.
2) Generate models/specs:
   - python scripts/render_formalizations.py true-dual-tract/chunks/chunk-NN.constraints.json
3) Solve:
   - minizinc true-dual-tract/chunks/chunk-NN.mzn
4) Prove:
   - add chunk-NN.lean to your Lean project and build
5) Cross-check constraints equivalence (MiniZinc ↔ Lean).

## Quick start
- Render:
  - python scripts/render_formalizations.py true-dual-tract/chunks/chunk-01.constraints.json
- Solve:
  - minizinc true-dual-tract/chunks/chunk-01.mzn

See index.md for checklist and status.
