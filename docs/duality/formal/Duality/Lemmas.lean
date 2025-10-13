/- Reusable lemma patterns (aligned with docs) -/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Duality.Base

namespace Duality

/-- tractMinimum: sum over a contiguous dimension range ≥ k -/
def tractMinimum (x : X8) (startIdx endIdx k : Nat) : Prop :=
  let vals := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8]
  (vals.drop (startIdx - 1)).take (endIdx - startIdx + 1) |>.foldl (· + ·) 0 ≥ k

instance (x : X8) (startIdx endIdx k : Nat) : Decidable (tractMinimum x startIdx endIdx k) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- uniformityConstraint: all dims in [start..end] ≥ k -/
def uniformityConstraint (x : X8) (startIdx endIdx k : Nat) : Prop :=
  let vals := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8]
  ∀ d ∈ ((vals.drop (startIdx - 1)).take (endIdx - startIdx + 1)), d ≥ k

instance (x : X8) (startIdx endIdx k : Nat) : Decidable (uniformityConstraint x startIdx endIdx k) :=
  inferInstanceAs (Decidable (∀ d ∈ _, d ≥ k))

/-- structureWellFormed: placeholder structural predicate (customize later) -/
def structureWellFormed (_ : X8) : Prop :=
  True  -- Replace with concrete invariants when defined

instance (x : X8) : Decidable (structureWellFormed x) :=
  inferInstanceAs (Decidable True)

/-- tractBalance: |T_int - T_ext| ≤ δ using helpers -/
def tractBalance (x : X8) (δ : Nat) : Prop :=
  Int.natAbs (Int.ofNat (T_int x) - Int.ofNat (T_ext x)) ≤ δ

instance (x : X8) (δ : Nat) : Decidable (tractBalance x δ) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- bridgeBalance: |v1 - v2| ≤ δ -/
def bridgeBalance (v1 v2 δ : Nat) : Prop :=
  (v1 : Int) - v2 ≤ δ ∧ (v2 : Int) - v1 ≤ δ

instance (v1 v2 δ : Nat) : Decidable (bridgeBalance v1 v2 δ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- dimensionFloor: xi ≥ k -/
def dimensionFloor (xi k : Nat) : Prop := xi ≥ k

instance (xi k : Nat) : Decidable (dimensionFloor xi k) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- primeAlignment: xi % p = 0 -/
def primeAlignment (xi p : Nat) : Prop := xi % p = 0

instance (xi p : Nat) : Decidable (primeAlignment xi p) :=
  inferInstanceAs (Decidable (_ = _))

/-- noDominance: pairwise diff ≤ Δ -/
def noDominance (vals : List Nat) (Δ : Nat) : Prop :=
  ∀ v1 ∈ vals, ∀ v2 ∈ vals, (v1 : Int) - v2 ≤ Δ ∧ (v2 : Int) - v1 ≤ Δ

instance (vals : List Nat) (Δ : Nat) : Decidable (noDominance vals Δ) :=
  inferInstanceAs (Decidable (∀ v1 ∈ vals, ∀ v2 ∈ vals, _))

/-- Scaling law types for Chunk 15 (stub definitions) -/
inductive ScalingLaw where
  | prime_based : ScalingLaw
deriving DecidableEq, Repr

def scaling_law : ScalingLaw := ScalingLaw.prime_based
def prime_based : ScalingLaw := ScalingLaw.prime_based

end Duality
