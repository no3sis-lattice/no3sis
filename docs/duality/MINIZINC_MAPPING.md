# MiniZinc Mapping Guide (8D Manifold, Monster Primes, Gödelization)

Purpose
- Translate chunk constraints into MiniZinc models that:
  - Assign 8D coordinates x[1..8] with unit-sum (discrete sum = N)
  - Respect Monster Group prime structure via parameter set P
  - Optionally enforce emoji→prime mappings and Gödel encodings
  - Optimize semantic coherence (e.g., neighbor distance minimization)

Core patterns
- 8D unitary:
  - Decision: array[1..8] of var 0..N: x;
  - constraint sum(i in 1..8)(x[i]) = N;

- Monster primes:
  - set of int: P = {2,3,5,7,11,13,17,19};

- Emoji-prime mapping (if provided):
  - array[int] of int: emoji_idx = ...; % data
  - array[int] of var P: prime_assign;   % enforce prime choice from P

- Neighbor similarity objective (optional):
  - Given adjacency list A, minimize sum over edges (dist(x_u, x_v));
  - dist choices: L1/L2 over discrete x; or projection_fit vs embeddings.

- Gödelization (optional):
  - Encode attributes into a composite integer; enforce factorization constraints
  - Note: keep numbers bounded; consider big-int libraries if needed, or encode factor logic with constraints.

Tips
- Start with satisfy; add objective only after feasibility is reliable.
- For stability, prefer discrete domain (N=100) early; move to reals later if solver backend supports it.
- Keep chunk-local; add inter-chunk constraints in higher-level models.

Cross-check with Lean
- Encode identical invariants as Lean propositions.
- Maintain a constraints checksum (sorted list of names/expr) to detect drift.
