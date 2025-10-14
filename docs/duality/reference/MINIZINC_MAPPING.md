# MiniZinc Mapping Guide (8D Manifold, Monster Primes, Gödelization)

## Purpose
Translate chunk constraints into MiniZinc models that:
- Assign 8D coordinates x[1..8] with unit-sum (discrete sum = N)
- Respect Monster Group prime structure via parameter set P
- Optionally enforce emoji→prime mappings and Gödel encodings
- Optimize semantic coherence (e.g., neighbor distance minimization)

## Core Patterns

### 8D Unitary Constraint
```minizinc
array[1..8] of var 0..N: x;
constraint sum(i in 1..8)(x[i]) = N;
```

### Monster Primes
```minizinc
set of int: P = {2,3,5,7,11,13,17,19};
```

### Emoji-Prime Mapping (Optional)
```minizinc
array[int] of int: emoji_idx = ...; % data
array[int] of var P: prime_assign;   % enforce prime choice from P
```

### Neighbor Similarity Objective (Optional)
```minizinc
% Given adjacency list A, minimize sum over edges (dist(x_u, x_v))
% dist choices: L1/L2 over discrete x; or projection_fit vs embeddings
```

### Gödelization (Optional)
```minizinc
% Encode attributes into composite integer; enforce factorization constraints
% Note: Keep numbers bounded; consider big-int libraries if needed
```

## Corner Cases and Operator Details

### Absolute Value
**JSON DSL:**
```json
{"name": "balance", "expr": "abs(x[1] - x[2]) <= k"}
```

**MiniZinc:**
```minizinc
% constraint: balance
constraint abs(x[1] - x[2]) <= k;
```

**Notes:**
- MiniZinc `abs()` builtin handles automatic reification
- Works for both integer and float domains
- Solver backend (Gecode/Chuffed) determines efficiency

**Lean Equivalent:**
```lean
-- constraint: balance
((x.x1 : Int) - x.x2 ≤ k ∧ (x.x2 : Int) - x.x1 ≤ k)
```

---

### Summation Constraints
**JSON DSL:**
```json
{"name": "external_min", "expr": "sum(i in 1..4)(x[i]) >= threshold"}
```

**MiniZinc:**
```minizinc
% constraint: external_min
constraint sum(i in 1..4)(x[i]) >= threshold;
```

**Notes:**
- MiniZinc `sum` is a builtin aggregator
- Automatically optimized by solver (decomposition if needed)

**Lean Equivalent:**
```lean
-- constraint: external_min
(x.x1 + x.x2 + x.x3 + x.x4 >= threshold)
```

---

### Universal Quantifiers (forall)
**JSON DSL:**
```json
{"name": "min_per_layer", "expr": "forall(i in 1..4)(x[i] >= 3)"}
```

**MiniZinc:**
```minizinc
% constraint: min_per_layer
constraint forall(i in 1..4)(x[i] >= 3);
```

**Notes:**
- MiniZinc `forall` is lazy (short-circuits on first false)
- Reified automatically if used in complex expressions

**Lean Equivalent:**
```lean
-- constraint: min_per_layer
(x.x1 >= 3 ∧ x.x2 >= 3 ∧ x.x3 >= 3 ∧ x.x4 >= 3)
```

**Alternative (Indexed):**
```lean
(∀ (i : Fin 4), [x.x1, x.x2, x.x3, x.x4][i.val]'(by omega) >= 3)
```

---

### Cardinality Constraints
**JSON DSL:**
```json
{"name": "sparse", "expr": "count(i in 1..8)(x[i] > 0) <= 5"}
```

**MiniZinc:**
```minizinc
% constraint: sparse
constraint sum(i in 1..8)(x[i] > 0) <= 5;
```

**Notes:**
- MiniZinc coerces `bool` to `int` (false=0, true=1) via `bool2int`
- Implicit coercion in arithmetic contexts
- Explicit: `sum(i in 1..8)(bool2int(x[i] > 0)) <= 5`

**Lean Equivalent:**
```lean
-- constraint: sparse
(List.sum (List.map (fun xi => if xi > 0 then 1 else 0) [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8]) <= 5)
```

---

### Integer Division and Modulo
**JSON DSL:**
```json
{"name": "prime_align", "expr": "x[1] % 2 == 0 && x[2] % 3 == 0"}
```

**MiniZinc:**
```minizinc
% constraint: prime_align
constraint x[1] mod 2 = 0 /\ x[2] mod 3 = 0;
```

**Notes:**
- MiniZinc uses `mod` keyword (not `%`)
- Conjunction: `/\` (not `&&`)
- Integer division: `div` (not `/`)

**Lean Equivalent:**
```lean
-- constraint: prime_align
(x.x1 % 2 = 0 ∧ x.x2 % 3 = 0)
```

---

### Conditional Constraints (Reification)
**JSON DSL:**
```json
{"name": "conditional", "expr": "x[1] > 10 -> x[2] >= 5"}
```

**MiniZinc:**
```minizinc
% constraint: conditional
constraint (x[1] > 10) -> (x[2] >= 5);
```

**Notes:**
- MiniZinc implication is built-in: `a -> b` ≡ `¬a ∨ b`
- Reification handled automatically by solver
- Equivalent: `constraint not(x[1] > 10) \/ (x[2] >= 5);`

**Lean Equivalent:**
```lean
-- constraint: conditional
(x.x1 > 10 → x.x2 >= 5)
```

---

## Known Limitations

### 1. Complex Quantifier Nesting
**Unsupported:**
```json
{"expr": "forall(i in 1..8)(exists(j in 1..8)(x[i] + x[j] == N/2))"}
```

**Reason:** Nested quantifiers require solver-specific decomposition or explicit enumeration

**Workaround:** Manually expand or use auxiliary boolean variables

---

### 2. Non-Linear Constraints
**Limited Support:**
```json
{"expr": "x[1] * x[2] <= 100"}
```

**Notes:**
- Works in MiniZinc (non-linear solvers like Gecode handle it)
- May be slow for large domains
- Lean requires separate decidability proof

**Lean Challenge:**
```lean
-- May need custom decidability instance or computational reflection
instance : Decidable (x.x1 * x.x2 <= 100) := by decide
```

---

### 3. Floating Point Operations
**Not Recommended:**
```json
{"expr": "x[1] / 2.0 >= 5.5"}
```

**Reason:** Synapse uses discrete N=100 for integer optimization

**Workaround:** Scale to integers: `x[1] >= 11` (5.5 * 2 = 11)

---

## Translation Rules Summary

| JSON Operator | MiniZinc | Lean | Notes |
|--------------|----------|------|-------|
| `+`, `-`, `*` | Same | Same | Standard arithmetic |
| `/` | `div` | `/` | Integer division |
| `%` | `mod` | `%` | Modulo |
| `==` | `=` | `=` | Equality |
| `!=` | `!=` | `≠` | Inequality |
| `&&` | `/\` | `∧` | Conjunction |
| `\|\|` | `\/` | `∨` | Disjunction |
| `!` | `not` | `¬` | Negation |
| `->` | `->` | `→` | Implication |
| `abs(a)` | `abs(a)` | Cast to Int then abs | Absolute value |
| `sum(...)` | `sum(...)` | Expand or List.sum | Summation |
| `forall(...)` | `forall(...)` | `∀` or expand | Universal quantifier |
| `exists(...)` | Complex | `∃` | Existential (witness) |

---

## Best Practices

1. **Start Simple:** Begin with `solve satisfy;`, add objectives later
2. **Annotate Constraints:** Use `% constraint: name` comments for traceability
3. **Validate Incrementally:** Test each constraint addition with MiniZinc
4. **Check Decidability:** Ensure Lean props have decidable instances
5. **Maintain Parity:** Run `cross_check_all.py` after changes

---

## Cross-Check with Lean

To maintain rigorous equivalence:
1. **Constraint Names:** Must match across JSON/MZN/Lean
2. **Checksums:** `cross_check_all.py` verifies SHA-256 parity
3. **Witnesses:** MiniZinc solutions become Lean constructive proofs
4. **Decidability:** Every `domainConstraints` needs `instance : Decidable`

**Example Workflow:**
```bash
# 1. Edit JSON constraints
vim true-dual-tract/chunks/chunk-06.constraints.json

# 2. Render to MZN + Lean
python scripts/render_formalizations.py true-dual-tract/chunks/chunk-06.constraints.json

# 3. Solve with MiniZinc
minizinc formal/Duality/Chunks/Chunk06.mzn

# 4. Inject witness to Lean
python scripts/inject_witnesses.py 06 --solution="[91, 3, 3, 3, 0, 0, 0, 0]"

# 5. Verify parity
python scripts/cross_check_all.py --chunks 06
```

---

## Equivalence Guarantees and Formal Semantics

### Soundness Guarantee

**For each constraint `c` in JSON:**

1. **MiniZinc Encoding:** `render_constraints_to_mzn(c)` produces syntactically valid MiniZinc
2. **Lean Encoding:** Direct syntactic translation to Lean `Prop`
3. **Guarantee:** If MiniZinc model has solution `s`, then Lean witness constructed from `s` satisfies `domainConstraints`

**Formal Statement:**
```
∀ c ∈ Constraints, ∀ s ∈ Solutions(MZN(c)),
  witness_from_solution(s) ⊨ Lean(c)
```

**Proof Obligations:**
1. MiniZinc solution exists → Lean witness is well-typed
2. MiniZinc solution satisfies constraint → Lean proof by `omega` or `decide`
3. Checksum parity: SHA256(names_mzn) = SHA256(names_lean)

---

### Completeness (Best Effort)

**MiniZinc Solver Completeness:**
- Depends on backend (Gecode, Chuffed, OR-Tools)
- **Finite domain guarantee:** For discrete N=100, solver explores full space
- **Termination:** Guaranteed for CSP problems (no unbounded quantifiers)

**Lean Constructive Proofs:**
- If Lean theorem proven constructively (no `admit`), then witness exists
- Witness can be extracted and fed to MiniZinc for validation
- **Bidirectional verification:** Lean proof ⇒ MiniZinc SAT

---

### Translation Correctness

**Operator Semantics:**

| JSON Expr | MiniZinc Semantics | Lean Semantics | Equivalence |
|-----------|-------------------|----------------|-------------|
| `x[i] + x[j]` | Integer addition | `Nat.add` | ✅ Exact |
| `x[i] - x[j]` | Integer subtraction | Cast to `Int` | ⚠️ Domain change |
| `abs(a - b)` | `|a - b|` | `\|(a:Int) - b\|` | ✅ Exact (after cast) |
| `sum(i in S)(...)` | Aggregator builtin | Expansion or List.sum | ✅ Extensional equality |
| `forall(i in S)(P)` | Lazy conjunction | Strict conjunction (`∧`) | ⚠️ Evaluation order differs |
| `a -> b` | `¬a ∨ b` | `a → b` | ✅ Logical equivalence |

**Key Point:** Evaluation order differences don't affect **semantic equivalence** (final truth value).

---

### Traceability and Drift Detection

Each constraint has a **stable identifier** appearing consistently across modalities:

**JSON:**
```json
{"name": "external_min_viable", "expr": "x[1] + x[2] + x[3] >= 30"}
```

**MiniZinc:**
```minizinc
% constraint: external_min_viable
constraint x[1] + x[2] + x[3] >= 30;
```

**Lean:**
```lean
-- constraint: external_min_viable
(x.x1 + x.x2 + x.x3 >= 30) ∧
```

**Checksum Verification:**
1. Extract names from all three modalities
2. Sort lexicographically
3. Compute SHA-256 hash
4. Verify: `hash(JSON) = hash(MZN) = hash(Lean)`

**If mismatch detected:**
- Status: `MISMATCH` in cross-check report
- CI fails (strict mode for pilots)
- Developer investigates diff sample

---

### Known Limitations and Approximations

#### 1. Integer vs Natural Domain
- **JSON/MZN:** Use integer arithmetic (can be negative)
- **Lean:** Uses `Nat` (non-negative)
- **Approximation:** Cast to `Int` when subtraction needed
- **Validation:** Witness values always non-negative (ensured by unit-sum + non-negativity)

#### 2. Solver-Dependent Behavior
- **MiniZinc:** Solution may vary by backend (Gecode vs Chuffed)
- **Lean:** Deterministic witness extraction
- **Guarantee:** All valid solutions accepted, but specific witness may differ

#### 3. Quantifier Expansion
- **Complex quantifiers:** May require manual Lean proof tactics
- **Simple quantifiers:** Automatically decidable via `omega`
- **Limitation:** Nested `∃∀` patterns not fully automated

---

### Verification Protocol

**For each chunk, the following must hold:**

1. **Name Parity:**
   ```
   SHA256(names_json) = SHA256(names_mzn) = SHA256(names_lean)
   ```

2. **SAT Parity:**
   ```
   MZN_SAT(chunk) ↔ Lean_SAT(chunk)
   ```

3. **Witness Validity:**
   ```
   ∀ s ∈ MZN_solutions, Lean.witness_valid(s) proves successfully
   ```

4. **Decidability:**
   ```
   Lean.domainConstraints has Decidable instance
   ```

5. **No Admits:**
   ```
   grep -r "admit" Chunk{NN}.lean → empty result (for proven chunks)
   ```

---

### Continuous Validation (CI Integration)

**On every commit to `docs/duality/**`:**

1. **JSON Schema Validation:**
   - All constraints conform to `chunk-constraints.schema.json`
   - Required fields present: `name`, `expr`

2. **MiniZinc Syntax Check:**
   - `minizinc --check-only Chunk{NN}.mzn` succeeds for all chunks

3. **Lean Build:**
   - `lake build Duality` succeeds
   - All pilot chunks (06, 09, 19) have proven theorems

4. **Cross-Check:**
   - Pilot chunks: **Strict mode** (CI fails on mismatch)
   - Other chunks: **Warn mode** (reports but doesn't fail)

5. **Regression Detection:**
   - Compare new report with baseline
   - Alert on parity loss for previously-OK chunks

---

### Error Recovery and Debugging

**If equivalence breaks:**

1. **Run Cross-Check:**
   ```bash
   python scripts/cross_check_all.py --chunks NN --format json
   ```

2. **Inspect Diff:**
   - Check which names are present/missing in each modality
   - Common cause: Missing `% constraint: name` comment in MZN

3. **Validate Individually:**
   ```bash
   # MiniZinc
   minizinc formal/Duality/Chunks/ChunkNN.mzn

   # Lean
   cd formal && lake build Duality.Chunks.ChunkNN
   ```

4. **Check Witness:**
   ```lean
   #eval decide (domainConstraints witness)  -- Should return true
   ```

5. **Re-Render if Needed:**
   ```bash
   python scripts/render_formalizations.py \
     true-dual-tract/chunks/chunk-NN.constraints.json --force
   ```

---

### Formal Verification Roadmap

**Current State (Phase 7):**
- ✅ 3/62 chunks: Name parity proven (06, 09, 19)
- ✅ 3/62 chunks: Constructive witnesses (non-trivial)
- ✅ Cross-check tool operational
- ⏳ 59/62 chunks: Need de-trivialization

**Phase 8 (Scaling):**
- Apply pilot pattern to remaining 59 chunks
- Add 2-3 non-trivial constraints per chunk
- Generate witnesses from MiniZinc solutions
- Achieve 100% name parity

**Phase 9 (Equivalence Lemmas):**
- Add `jsonSpec ↔ domainConstraints` theorem stubs
- Prove for pilot chunks first
- Document proof patterns for common cases

**Phase 10 (Full Rigor):**
- All 62 chunks: Proven equivalence theorems
- All 62 chunks: Decidable instances
- All 62 chunks: Non-degenerate constraints
- CI: Strict mode for all chunks

---

### References

1. **MiniZinc Semantics:** [https://www.minizinc.org/doc-2.8.5/en/spec.html](https://www.minizinc.org/doc-2.8.5/en/spec.html)
2. **Lean4 Propositions:** [https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html)
3. **SHA-256 Specification:** [FIPS PUB 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf)
4. **Cross-Check Tool:** `docs/duality/scripts/cross_check_all.py`
5. **Lean Translation Guide:** `docs/duality/LEAN_TRANSLATION_GUIDE.md`

---

**Document Version:** 1.1
**Last Updated:** 2025-10-12
**Status:** Active - Formal Semantics Documented

