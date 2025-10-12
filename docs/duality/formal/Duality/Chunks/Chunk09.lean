/-
Template Lean4 spec mirroring the MiniZinc constraints for a chunk.
-/

import Mathlib.Data.Nat.Basic

namespace Chunk09

def N : ℕ := 100

structure X8 where
  x1 x2 x3 x4 x5 x6 x7 x8 : Nat
deriving Repr

def unitary (x : X8) : Prop :=
  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N

-- Domain constraints: PILOT Corpus Callosum
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

-- Witness from MiniZinc: [7, 3, 0, 90, 0, 0, 0, 0]
def witness : X8 := ⟨7, 3, 0, 90, 0, 0, 0, 0⟩

theorem witness_valid : unitary witness ∧ domainConstraints witness := by
  constructor
  · rfl
  · constructor <;> try trivial
    constructor; omega  -- minimum: 7+3=10
    constructor; omega  -- balance: |7-3|=4<=5
    omega  -- modest: 7+3+0=10<=40

theorem exists_solution : ∃ x : X8, unitary x ∧ domainConstraints x :=
  ⟨witness, witness_valid⟩

end Chunk09
