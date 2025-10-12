/- Reusable lemma patterns (aligned with docs) -/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Duality.Base

namespace Duality

/-- tractMinimum: sum over a contiguous dimension range ≥ k -/
def tractMinimum (x : X8) (startIdx endIdx k : Nat) : Prop :=
  let vals := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8]
  (vals.drop (startIdx - 1)).take (endIdx - startIdx + 1) |>.foldl (· + ·) 0 ≥ k

/-- uniformityConstraint: all dims in [start..end] ≥ k -/
def uniformityConstraint (x : X8) (startIdx endIdx k : Nat) : Prop :=
  let vals := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8]
  List.All (fun d => d ≥ k) ((vals.drop (startIdx - 1)).take (endIdx - startIdx + 1))

/-- structureWellFormed: placeholder structural predicate (customize later) -/
def structureWellFormed (x : X8) : Prop :=
  True  -- Replace with concrete invariants when defined

/-- tractBalance: |T_int - T_ext| ≤ δ using helpers -/
def tractBalance (x : X8) (δ : Nat) : Prop :=
  Int.natAbs (Int.ofNat (tractSumInt x) - Int.ofNat (tractSumExt x)) ≤ δ

/-- bridgeBalance: |v1 - v2| ≤ δ -/
def bridgeBalance (v1 v2 δ : Nat) : Prop :=
  (v1 : Int) - v2 ≤ δ ∧ (v2 : Int) - v1 ≤ δ

/-- dimensionFloor: xi ≥ k -/
def dimensionFloor (xi k : Nat) : Prop := xi ≥ k

/-- primeAlignment: xi % p = 0 -/
def primeAlignment (xi p : Nat) : Prop := xi % p = 0

/-- noDominance: pairwise diff ≤ Δ -/
def noDominance (vals : List Nat) (Δ : Nat) : Prop :=
  ∀ v1 ∈ vals, ∀ v2 ∈ vals, (v1 : Int) - v2 ≤ Δ ∧ (v2 : Int) - v1 ≤ Δ

end Duality
