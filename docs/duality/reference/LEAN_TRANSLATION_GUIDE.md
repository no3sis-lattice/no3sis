# Lean4 Translation Reference for Synapse Duality Formalization

## Purpose
This guide provides canonical patterns for translating JSON constraint DSL into Lean4 propositions, ensuring semantic equivalence with MiniZinc models while maintaining decidability and constructive provability.

---

## Table of Contents
1. [Primitive Translations](#primitive-translations)
2. [Decidability Requirements](#decidability-requirements)
3. [Equivalence Pattern](#equivalence-pattern)
4. [Advanced Patterns](#advanced-patterns)
5. [Common Pitfalls](#common-pitfalls)
6. [Examples from Pilot Chunks](#examples-from-pilot-chunks)

---

## Primitive Translations

### Basic Arithmetic
| JSON DSL | Lean4 Proposition | Notes |
|----------|-------------------|-------|
| `x[i] + x[j] >= k` | `x.xi + x.xj >= k` | Direct translation |
| `x[i] - x[j] <= k` | `(x.xi : Int) - x.xj <= k` | Cast to Int for subtraction |
| `x[i] * x[j] == k` | `x.xi * x.xj = k` | Multiplication |
| `x[i] / k >= m` | `x.xi / k >= m` | Integer division (euclidean) |
| `x[i] % p == 0` | `x.xi % p = 0` | Modulo operation |

**Example:**
```json
{"name": "min_sum", "expr": "x[1] + x[2] + x[3] >= 30"}
```

```lean
-- constraint: min_sum
(x.x1 + x.x2 + x.x3 >= 30)
```

---

### Summation
| JSON DSL | Lean4 Strategy | Notes |
|----------|---------------|-------|
| `sum(i in 1..4)(x[i])` | Expand: `x.x1 + x.x2 + x.x3 + x.x4` | Preferred for small ranges |
| `sum(i in 1..8)(x[i])` | Use List.sum | For full 8D vector |

**Direct Expansion (Preferred):**
```json
{"name": "tract_sum", "expr": "sum(i in 1..4)(x[i]) >= sum(i in 5..8)(x[i])"}
```

```lean
-- constraint: tract_sum
(x.x1 + x.x2 + x.x3 + x.x4 >= x.x5 + x.x6 + x.x7 + x.x8)
```

**List-Based (Alternative):**
```lean
-- constraint: tract_sum
(List.sum [x.x1, x.x2, x.x3, x.x4] >= List.sum [x.x5, x.x6, x.x7, x.x8])
```

---

### Universal Quantifiers (forall)

**Strategy 1: Direct Expansion (Recommended for Small Ranges)**
```json
{"name": "min_each", "expr": "forall(i in 1..4)(x[i] >= 3)"}
```

```lean
-- constraint: min_each
(x.x1 >= 3 ∧ x.x2 >= 3 ∧ x.x3 >= 3 ∧ x.x4 >= 3)
```

**Strategy 2: Indexed Quantifier (For Generality)**
```lean
-- constraint: min_each
(∀ (i : Fin 4), [x.x1, x.x2, x.x3, x.x4][i.val]'(by omega) >= 3)
```

**When to Use Each:**
- **Expansion:** For ranges ≤ 8 (decidability automatic via omega)
- **Indexed:** When proving general lemmas about vector properties

---

### Absolute Value
```json
{"name": "balance", "expr": "abs(x[1] - x[2]) <= 5"}
```

```lean
-- constraint: balance
((x.x1 : Int) - x.x2 ≤ 5 ∧ (x.x2 : Int) - x.x1 ≤ 5)
```

**Key Point:** Cast to `Int` before subtraction to handle negative results.

---

### Cardinality (Counting)
```json
{"name": "sparse", "expr": "count(i in 1..8)(x[i] > 0) <= 5"}
```

```lean
-- constraint: sparse
(List.sum (List.map (fun xi => if xi > 0 then 1 else 0)
  [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8]) <= 5)
```

**Pattern:** Map boolean predicate to 0/1, then sum.

---

### Logical Operators
| JSON | Lean | Example |
|------|------|---------|
| `&&` | `∧` | `(a ∧ b)` |
| `\|\|` | `∨` | `(a ∨ b)` |
| `!` | `¬` | `¬a` |
| `->` | `→` | `(a → b)` |
| `==` | `=` | `x = y` |
| `!=` | `≠` | `x ≠ y` |

**Example:**
```json
{"name": "cond", "expr": "x[1] > 10 -> x[2] >= 5"}
```

```lean
-- constraint: cond
(x.x1 > 10 → x.x2 >= 5)
```

---

## Decidability Requirements

### The Golden Rule
**Every `domainConstraints` proposition must be computationally decidable.**

### Standard Pattern
```lean
instance : Decidable (domainConstraints x) := by
  unfold domainConstraints
  infer_instance  -- Works for arithmetic, comparisons, ∧, ∨, ¬
```

### When `infer_instance` Fails
If you encounter non-decidable propositions (rare in our 8D integer domain):

```lean
instance : Decidable (domainConstraints x) := by
  unfold domainConstraints
  -- Split into decidable components
  constructor
  · decide  -- First constraint
  · decide  -- Second constraint
  -- Continue for all constraints
```

### Testing Decidability
```lean
#eval decide (domainConstraints witness)  -- Should compile without errors
```

---

## Equivalence Pattern

### Per-Chunk Template
Every chunk should include an equivalence guarantee between the JSON spec and Lean formalization.

```lean
namespace ChunkNN

-- JSON specification (mechanically generated from constraints.json)
def jsonSpec (x : X8) : Prop :=
  -- Each constraint from JSON rendered as a Lean prop
  (x.x1 + x.x2 >= 10) ∧
  (x.x1 % 2 = 0) ∧
  True  -- Additional constraints...

-- Main domain constraints (hand-written or template-generated)
def domainConstraints (x : X8) : Prop :=
  -- constraint: bridge_minimum
  (x.x1 + x.x2 >= 10) ∧
  -- constraint: prime_alignment
  (x.x1 % 2 = 0) ∧
  True

-- Equivalence theorem
theorem json_equiv_domain : ∀ x, jsonSpec x ↔ domainConstraints x := by
  intro x
  unfold jsonSpec domainConstraints
  constructor
  · intro h; exact h  -- Forward direction
  · intro h; exact h  -- Backward direction

end ChunkNN
```

### Equivalence Proof Tactics
- **Simple cases:** `constructor <;> intro h <;> exact h`
- **Arithmetic:** `constructor <;> intro h <;> omega`
- **Mixed:** `constructor <;> (intro h; simp [*]; omega)`

---

## Advanced Patterns

### Nested Conditionals
```json
{"expr": "(x[1] > 10 && x[2] < 5) -> x[3] >= 20"}
```

```lean
((x.x1 > 10 ∧ x.x2 < 5) → x.x3 >= 20)
```

### Range Constraints
```json
{"expr": "x[1] >= 5 && x[1] <= 15"}
```

```lean
(5 <= x.x1 ∧ x.x1 <= 15)
```

**Alternative:** Use interval notation (requires Mathlib):
```lean
x.x1 ∈ Set.Icc 5 15  -- [5, 15] closed interval
```

### Pairwise Constraints
```json
{"expr": "forall(i in 1..7)(forall(j in i+1..8)(abs(x[i] - x[j]) <= 20))"}
```

**Strategy:** Expand outer loop, use indexed inner:
```lean
(∀ j, j > 0 → abs((x.x1 : Int) - [x.x2, x.x3, ..., x.x8][j]'_ ) <= 20) ∧
(∀ j, j > 1 → abs((x.x2 : Int) - [x.x3, ..., x.x8][j-1]'_ ) <= 20) ∧
-- Continue pattern...
```

**For Full Generality (Chunk 19 Example):**
```lean
(∀ (i j : Fin 8), i.val < j.val →
  let xi := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8][i.val]'(by omega)
  let xj := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8][j.val]'(by omega)
  (xi : Int) - xj ≤ 20 ∧ xj - xi ≤ 20)
```

---

## Common Pitfalls

### 1. Integer Underflow in Subtraction
**Wrong:**
```lean
x.x1 - x.x2 <= 5  -- Type error if x2 > x1 (Nat underflow)
```

**Right:**
```lean
(x.x1 : Int) - x.x2 <= 5  -- Cast to Int first
```

---

### 2. List Indexing Without Proof
**Wrong:**
```lean
[x.x1, x.x2, x.x3][i.val]  -- "index out of bounds" error
```

**Right:**
```lean
[x.x1, x.x2, x.x3][i.val]'(by omega)  -- Provide proof i.val < 3
```

---

### 3. Mixing Nat and Int
**Problem:**
```lean
x.x1 + (-5) >= 10  -- Type error: Nat doesn't have negation
```

**Solution:**
```lean
(x.x1 : Int) + (-5) >= 10  -- Cast entire expression to Int
```

**Alternative:**
```lean
x.x1 >= 15  -- Rewrite to avoid negation
```

---

### 4. Forgetting Decidability
**Symptom:** Theorem compiles, but `#eval` fails.

**Fix:**
```lean
-- Add decidability instance before theorems
instance : Decidable (domainConstraints x) := by
  unfold domainConstraints
  infer_instance
```

---

## Examples from Pilot Chunks

### Chunk 06: External Tract
```lean
def domainConstraints (x : X8) : Prop :=
  -- constraint: chunk_06_exists
  True ∧
  -- constraint: proof_required
  True ∧
  -- constraint: external_min_viable
  (x.x1 + x.x2 + x.x3 >= 30) ∧
  -- constraint: external_reactive_bias
  (x.x1 + x.x2 + x.x3 + x.x4 >= x.x5 + x.x6 + x.x7 + x.x8) ∧
  -- constraint: external_min_per_layer
  (x.x1 >= 3 ∧ x.x2 >= 3 ∧ x.x3 >= 3 ∧ x.x4 >= 3)
```

### Chunk 09: Corpus Callosum (Bridge)
```lean
def domainConstraints (x : X8) : Prop :=
  -- constraint: chunk_09_exists
  True ∧
  -- constraint: proof_required
  True ∧
  -- constraint: bridge_minimum
  (x.x1 + x.x2 >= 10) ∧
  -- constraint: bridge_balance
  ((x.x1 : Int) - x.x2 ≤ 5 ∧ (x.x2 : Int) - x.x1 ≤ 5) ∧
  -- constraint: bridge_modest
  (x.x1 + x.x2 + x.x3 <= 40)
```

### Chunk 19: Boss Orchestration (Complex)
```lean
def domainConstraints (x : X8) : Prop :=
  -- constraint: chunk_19_exists
  True ∧
  -- constraint: optimization_required
  True ∧
  -- constraint: boss_min_distribution
  (x.x1 >= 5 ∧ x.x2 >= 5 ∧ x.x3 >= 5 ∧ x.x4 >= 5 ∧
   x.x5 >= 5 ∧ x.x6 >= 5 ∧ x.x7 >= 5 ∧ x.x8 >= 5) ∧
  -- constraint: boss_balance_constraint (pairwise)
  (∀ (i j : Fin 8), i.val < j.val →
    let xi := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8][i.val]'(by omega)
    let xj := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8][j.val]'(by omega)
    (xi : Int) - xj ≤ 20 ∧ xj - xi ≤ 20) ∧
  -- constraint: boss_prime_alignment
  (x.x1 % 2 = 0 ∧ x.x2 % 3 = 0)
```

---

## Workflow Integration

### Step-by-Step Translation Process

1. **Read JSON Constraint:**
```json
{"name": "external_min_viable", "expr": "x[1] + x[2] + x[3] >= 30"}
```

2. **Identify Pattern:**
   - Type: Summation inequality
   - Range: Small (3 terms)
   - Strategy: Direct expansion

3. **Write Lean:**
```lean
-- constraint: external_min_viable
(x.x1 + x.x2 + x.x3 >= 30)
```

4. **Test Decidability:**
```bash
lean4 formal/Duality/Chunks/Chunk06.lean
# Should compile without errors
```

5. **Verify with Witness:**
```lean
def witness : X8 := ⟨91, 3, 3, 3, 0, 0, 0, 0⟩

theorem witness_valid : domainConstraints witness := by
  unfold domainConstraints witness
  constructor <;> try trivial
  constructor; omega  -- external_min_viable: 91+3+3=97>=30
  -- Continue for remaining constraints...
```

---

## Quick Reference Card

```lean
-- Standard imports
import Mathlib.Data.Nat.Basic

-- Structure definition
structure X8 where
  x1 x2 x3 x4 x5 x6 x7 x8 : Nat

-- Unit-sum constraint
def unitary (x : X8) : Prop :=
  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N

-- Domain constraints template
def domainConstraints (x : X8) : Prop :=
  -- constraint: name
  (lean_proposition) ∧
  -- constraint: name2
  (lean_proposition2) ∧
  True  -- Terminal

-- Decidability (required)
instance : Decidable (domainConstraints x) := by
  unfold domainConstraints
  infer_instance

-- Witness and proof
def witness : X8 := ⟨...⟩

theorem witness_valid : unitary witness ∧ domainConstraints witness := by
  constructor
  · rfl  -- unitary check
  · constructor <;> omega  -- domain constraints

-- Existence theorem
theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x :=
  ⟨witness, witness_valid⟩
```

---

## Additional Resources

- **Lean4 Documentation:** [https://lean-lang.org/lean4/doc/](https://lean-lang.org/lean4/doc/)
- **Mathlib4 Nat Docs:** [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Basic.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Basic.html)
- **Omega Tactic:** [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Omega.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Omega.html)
- **Cross-Check Tool:** `docs/duality/scripts/cross_check_all.py`

---

## Troubleshooting

### "Type mismatch" errors
- Check Nat vs Int casts
- Ensure list indices have proofs

### "Failed to synthesize Decidable instance"
- Add manual `instance` declaration
- Break complex props into decidable components

### Witness proof fails with "unsolved goals"
- Check arithmetic: Does witness actually satisfy constraints?
- Use `#eval` to test intermediate expressions
- Try `omega`, `decide`, or `norm_num` tactics

### Parity check fails
- Ensure constraint names match JSON exactly
- Verify `-- constraint: name` comments present
- Run `cross_check_all.py --chunks NN` to diagnose

---

**Document Version:** 1.0
**Last Updated:** 2025-10-12
**Status:** Active - Part of Rigorous Formalization Initiative Phase 2
