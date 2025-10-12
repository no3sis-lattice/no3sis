/-
Template Lean4 spec mirroring the MiniZinc constraints for a chunk.
-/

import Mathlib.Data.Nat.Basic

namespace Chunk19

def N : ℕ := 100

structure X8 where
  x1 x2 x3 x4 x5 x6 x7 x8 : Nat
deriving Repr

def unitary (x : X8) : Prop :=
  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N

-- Domain constraints: PILOT non-trivial constraints
def domainConstraints (x : X8) : Prop :=
  -- constraint: chunk_19_exists
  True ∧
  -- constraint: optimization_required
  True ∧
  -- constraint: boss_min_distribution
  (x.x1 >= 5 ∧ x.x2 >= 5 ∧ x.x3 >= 5 ∧ x.x4 >= 5 ∧ x.x5 >= 5 ∧ x.x6 >= 5 ∧ x.x7 >= 5 ∧ x.x8 >= 5) ∧
  -- constraint: boss_balance_constraint
  (∀ (i j : Fin 8), (if i.val < j.val then
    let xi := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8][i.val]'(by omega)
    let xj := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8][j.val]'(by omega)
    (xi : Int) - xj ≤ 20 ∧ xj - xi ≤ 20
  else True)) ∧
  -- constraint: boss_prime_alignment
  (x.x1 % 2 = 0 ∧ x.x2 % 3 = 0)

-- Witness from MiniZinc solution: [6, 6, 25, 25, 23, 5, 5, 5]
def witness : X8 := ⟨6, 6, 25, 25, 23, 5, 5, 5⟩

-- Verify witness satisfies constraints
theorem witness_valid : unitary witness ∧ domainConstraints witness := by
  constructor
  · -- unitary: 6+6+25+25+23+5+5+5 = 100
    rfl
  · -- domainConstraints
    constructor
    · trivial  -- chunk_19_exists
    constructor
    · trivial  -- optimization_required
    constructor
    · -- boss_min_distribution: all >= 5
      constructor <;> omega
    constructor
    · -- boss_balance_constraint: max diff <= 20
      intro i j
      split <;> try trivial
      omega
    · -- boss_prime_alignment
      constructor <;> rfl

-- Existence theorem proven by witness
theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x :=
  ⟨witness, witness_valid⟩

end Chunk19
