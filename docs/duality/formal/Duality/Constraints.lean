/-
Reusable Constraint Lemmas for Dual-Tract Formalization
Phase 5: DRY-compliant lemma library with decidability instances

These lemmas represent high-frequency patterns discovered in Phase 4
corpus analysis. Each lemma includes decidability for computational verification.

Usage:
  import Duality.Constraints
  open Duality

  def domainConstraints (x : X8) : Prop :=
    dimensionFloor x.x1 1 ∧
    tractMinimum (T_int x) 10 ∧
    ...
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Duality.Base

namespace Duality

open Duality

-- ============================================================================
-- Core Dimensional Lemmas
-- ============================================================================

/-- Dimensional floor: single dimension has minimum value
    Pattern frequency: 52/62 chunks (84%) -/
def dimensionFloor (dimVal minVal : Nat) : Prop :=
  dimVal ≥ minVal

instance (dimVal minVal : Nat) : Decidable (dimensionFloor dimVal minVal) :=
  inferInstanceAs (Decidable (dimVal ≥ minVal))


/-- Tract minimum: sum of dimensions ≥ threshold
    Pattern frequency: 54/62 chunks (87%)
    Used for both T_int and T_ext validation -/
def tractMinimum (tractSum minTotal : Nat) : Prop :=
  tractSum ≥ minTotal

instance (tractSum minTotal : Nat) : Decidable (tractMinimum tractSum minTotal) :=
  inferInstanceAs (Decidable (tractSum ≥ minTotal))


/-- Uniformity: all dimensions in range satisfy minimum
    Pattern frequency: 32/62 chunks (52%) -/
def uniformityConstraint (dims : List Nat) (minVal : Nat) : Prop :=
  ∀ d ∈ dims, d ≥ minVal

-- Simple decidability via List.all
instance (dims : List Nat) (minVal : Nat) : Decidable (uniformityConstraint dims minVal) := by
  unfold uniformityConstraint
  infer_instance


-- ============================================================================
-- Tract Balance Lemmas (M_syn - Emergent Meta-Pattern)
-- ============================================================================

/-- Universal tract balance: |T_int - T_ext| ≤ threshold
    Pattern frequency: 60/62 chunks (97%)
    Novelty score: 0.968 (highest consciousness contribution)

    This is an EMERGENT META-PATTERN discovered through corpus analysis.
    Nearly all chunks enforce equilibrium between internal (reflection)
    and external (action) tracts without explicit design. -/
def tractBalance (T_int T_ext threshold : Nat) : Prop :=
  (T_int : Int) - T_ext ≤ threshold ∧ (T_ext : Int) - T_int ≤ threshold

instance (T_int T_ext threshold : Nat) : Decidable (tractBalance T_int T_ext threshold) :=
  inferInstanceAs (Decidable ((T_int : Int) - T_ext ≤ threshold ∧ (T_ext : Int) - T_int ≤ threshold))


/-- Bridge balance: |v1 - v2| ≤ threshold
    Used in bridge/orchestration chunks for component symmetry -/
def bridgeBalance (v1 v2 threshold : Nat) : Prop :=
  (v1 : Int) - v2 ≤ threshold ∧ (v2 : Int) - v1 ≤ threshold

instance (v1 v2 threshold : Nat) : Decidable (bridgeBalance v1 v2 threshold) :=
  inferInstanceAs (Decidable ((v1 : Int) - v2 ≤ threshold ∧ (v2 : Int) - v1 ≤ threshold))


-- ============================================================================
-- Specialized Lemmas
-- ============================================================================

/-- Prime alignment: dimension divisible by prime
    Pattern frequency: 3/62 chunks (5%) - boss/orchestration only
    Demonstrates Pneuma Axiom I (Bifurcation: context density through prime compression) -/
def primeAlignment (dimVal p : Nat) : Prop :=
  dimVal % p = 0

instance (dimVal p : Nat) : Decidable (primeAlignment dimVal p) :=
  inferInstanceAs (Decidable (dimVal % p = 0))


/-- No dominance: no dimension dominates others by more than maxDiff
    Pattern frequency: 10/62 chunks (16%) - structural integrity -/
def noDominance (dims : List Nat) (maxDiff : Nat) : Prop :=
  ∀ v1 ∈ dims, ∀ v2 ∈ dims,
    (v1 : Int) - v2 ≤ maxDiff ∧ (v2 : Int) - v1 ≤ maxDiff

-- Decidability via nested List.all
instance (dims : List Nat) (maxDiff : Nat) : Decidable (noDominance dims maxDiff) := by
  unfold noDominance
  infer_instance


-- ============================================================================
-- Composite X8 Helpers
-- ============================================================================

/-- Internal tract (T_int): sum of first 4 dimensions -/
def T_int (x : X8) : Nat := x.x1 + x.x2 + x.x3 + x.x4

/-- External tract (T_ext): sum of last 4 dimensions -/
def T_ext (x : X8) : Nat := x.x5 + x.x6 + x.x7 + x.x8

/-- All 8 dimensions as a list (for uniformity checks) -/
def allDims (x : X8) : List Nat := [x.x1, x.x2, x.x3, x.x4, x.x5, x.x6, x.x7, x.x8]

/-- Tract balance for X8 (syntactic sugar) -/
def X8_tractBalance (x : X8) (threshold : Nat) : Prop :=
  tractBalance (T_int x) (T_ext x) threshold

instance (x : X8) (threshold : Nat) : Decidable (X8_tractBalance x threshold) :=
  inferInstanceAs (Decidable (tractBalance (T_int x) (T_ext x) threshold))


-- ============================================================================
-- Usage Examples (commented out, for documentation)
-- ============================================================================

/-
Example 1: Chunk with dimensional floor and tract minimum

def domainConstraints (x : X8) : Prop :=
  dimensionFloor x.x1 1 ∧
  tractMinimum (T_int x) 10 ∧
  uniformityConstraint (allDims x) 1

instance : Decidable (domainConstraints x) := by
  unfold domainConstraints
  infer_instance  -- All lemmas have decidability, so this works automatically


Example 2: Chunk with tract balance (M_syn pattern)

def domainConstraints (x : X8) : Prop :=
  X8_tractBalance x 10 ∧
  tractMinimum (T_int x) 20

instance : Decidable (domainConstraints x) := by
  unfold domainConstraints
  infer_instance


Example 3: Boss chunk with prime alignment

def domainConstraints (x : X8) : Prop :=
  primeAlignment x.x1 2 ∧
  primeAlignment x.x2 3 ∧
  noDominance (allDims x) 20

instance : Decidable (domainConstraints x) := by
  unfold domainConstraints
  infer_instance
-/

end Duality
