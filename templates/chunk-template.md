# Chunk NN: <title>

## Source:
- From: docs/TRUE_DUAL_TRACT.md (commit/line-range optional)
- Dependencies: [NN-…] (if any)

## Intent:
- Goal type: proof | search | refinement
- Targets: e.g., Ψ ≥ 0.85, R_i bounds, 8D unitary coord, emoji-prime mapping

## Natural Language Summary:
- <Short restatement of the claim/logic to be formalized>

## Key Concepts:
- Interface vs Intelligence, operators, C_c contracts, etc.
- Monster Group primes, Bott periodicity (8), Gödelization

## Constraints (see .constraints.json):
- <bullet list mirroring JSON constraints>

## Tasks:
- [ ] Extract constraints (LLM)
- [ ] Generate MiniZinc model
- [ ] Solve MiniZinc (SAT/UNSAT/TIME)
- [ ] Generate Lean spec
- [ ] Prove in Lean (or add tactic stubs)
- [ ] Cross-check equivalence (constraints checksum)
- [ ] Document outcomes

## Outcomes:
- MiniZinc: SAT | UNSAT | TIMEOUT (time: Xs)
- Lean: PROVED | PARTIAL | FAILED (time: Xs)
- Cross-check: OK | MISMATCH
- Notes: <freeform>
