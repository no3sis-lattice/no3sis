/-
Template Lean4 spec mirroring the MiniZinc constraints for a chunk.
-/

import Mathlib.Data.Nat.Basic

namespace Chunk06

def N : ℕ := 100

structure X8 where
  x1 x2 x3 x4 x5 x6 x7 x8 : Nat
deriving Repr

def unitary (x : X8) : Prop :=
  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N

-- Domain constraints: PILOT External Tract
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

-- Witness from MiniZinc: [91, 3, 3, 3, 0, 0, 0, 0]
def witness : X8 := ⟨91, 3, 3, 3, 0, 0, 0, 0⟩

theorem witness_valid : unitary witness ∧ domainConstraints witness := by
  constructor
  · rfl  -- unitary
  · constructor <;> try trivial
    constructor; omega  -- min_viable: 91+3+3=97>=30
    constructor; omega  -- reactive_bias: 100>=0
    omega  -- min_per_layer: all >= 3

theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x :=
  ⟨witness, witness_valid⟩

end Chunk06
