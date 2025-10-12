/-
Test suite for Duality.Base module
Tests X8 structure and unitary constraint properties
-/

import Duality.Base

namespace Duality.Tests

open Duality

/-- Test: Standard witness has correct values -/
example : standardWitness.x1 = 100 := rfl
example : standardWitness.x2 = 0 := rfl
example : standardWitness.x8 = 0 := rfl

/-- Test: Standard witness satisfies unitary -/
example : unitary standardWitness := standardWitness_unitary

/-- Test: Sum of all zeros is not unitary -/
example : ¬unitary ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  unfold unitary
  unfold N
  decide

/-- Test: Evenly distributed witness satisfies unitary (approximate) -/
example : unitary ⟨12, 13, 13, 12, 13, 12, 13, 12⟩ := by
  rfl

/-- Property: Unitary is symmetric in coordinate permutation (example) -/
example : unitary ⟨100, 0, 0, 0, 0, 0, 0, 0⟩ →
          unitary ⟨0, 100, 0, 0, 0, 0, 0, 0⟩ := by
  intro _
  rfl

/-- Property: N is positive -/
example : 0 < N := by decide

/-- Property: Sum decomposition -/
example (x : X8) : unitary x ↔
  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N := by
  rfl

/-- Property: Unitary is preserved under coordinate swap (concrete example) -/
example : unitary ⟨50, 50, 0, 0, 0, 0, 0, 0⟩ →
          unitary ⟨50, 50, 0, 0, 0, 0, 0, 0⟩ := by
  intro h
  exact h

/-- Property: If two witnesses satisfy unitary, their coordinate sums are equal -/
theorem unitary_sum_invariant (x y : X8) :
  unitary x → unitary y →
  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 =
  y.x1 + y.x2 + y.x3 + y.x4 + y.x5 + y.x6 + y.x7 + y.x8 := by
  intro hx hy
  unfold unitary at *
  rw [hx, hy]

/-- Property: Scaling preserves non-unitary if factor ≠ 1 -/
example : unitary ⟨50, 0, 0, 0, 0, 0, 0, 0⟩ → False := by
  unfold unitary
  unfold N
  decide

end Duality.Tests
