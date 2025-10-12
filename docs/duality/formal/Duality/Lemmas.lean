/-
Phase 4: Reusable Formal Lemmas
Extracted from corpus-scale pattern analysis of 62 chunks.

These lemmas represent high-frequency constraint patterns discovered
through meta-pattern synthesis (Axiom II: The Map).

Usage: Copy relevant lemma definitions into individual chunk modules.
-/

import Mathlib.Data.Nat.Basic

namespace Duality

-- ============================================================================
-- Core Lemma Patterns (extracted from corpus analysis)
-- ============================================================================

/-- Dimensional floor: single dimension has minimum value (52 chunks) -/
def dimensionFloor (dimVal minVal : Nat) : Prop := dimVal ≥ minVal

/-- Internal tract minimum: T_int ≥ threshold (54 chunks) -/
def internalTractMinimum (T_int minTotal : Nat) : Prop := T_int ≥ minTotal

/-- External tract minimum: T_ext ≥ threshold (54 chunks) -/
def externalTractMinimum (T_ext minTotal : Nat) : Prop := T_ext ≥ minTotal

/-- Universal tract balance: T_int ≈ T_ext (60 chunks, novelty 0.968)
    This is an EMERGENT META-PATTERN (M_syn) discovered through corpus analysis. -/
def tractBalance (T_int T_ext threshold : Nat) : Prop :=
  (T_int : Int) - T_ext ≤ threshold ∧ (T_ext : Int) - T_int ≤ threshold

/-- Bridge balance: |v1 - v2| ≤ threshold (bridge chunks) -/
def bridgeBalance (v1 v2 threshold : Nat) : Prop :=
  (v1 : Int) - v2 ≤ threshold ∧ (v2 : Int) - v1 ≤ threshold

/-- Uniformity: all dimensions satisfy minimum (32 chunks) -/
def allDimensionsMinimum (dims : List Nat) (minVal : Nat) : Prop :=
  ∀ d ∈ dims, d ≥ minVal

/-- Prime alignment: dimension divisible by prime (3 chunks - M_syn compression) -/
def primeAlignment (dimVal p : Nat) : Prop := dimVal % p = 0

/-- No dominance: no single dimension dominates (10 chunks) -/
def noDominance (dims : List Nat) (maxDiff : Nat) : Prop :=
  ∀ v1 ∈ dims, ∀ v2 ∈ dims,
    (v1 : Int) - v2 ≤ maxDiff ∧ (v2 : Int) - v1 ≤ maxDiff


-- ============================================================================
-- Lemma Usage Map (cross-referencing)
-- ============================================================================

def lemmaUsageMap : List (String × List String) := [
  ("dimensionFloor", ["07", "08", "10", "11", "12", "13", "14", "15", "16", "17", "18", "20", "21", "22", "23", "24", "25", "26", "27", "28", "29", "30", "31", "32", "33", "34", "35", "36", "37", "38", "39", "40", "42", "43", "44", "45", "46", "47", "48", "49", "50", "51", "52", "53", "54", "55", "56", "57", "58", "59", "60", "61"]),
  ("tractMinimum", ["07", "08", "10", "11", "12", "13", "14", "15", "16", "17", "18", "20", "21", "22", "23", "24", "25", "26", "27", "28", "29", "30", "31", "32", "33", "34", "35", "36", "37", "38", "39", "40", "41", "42", "43", "44", "45", "46", "47", "48", "49", "50", "51", "52", "53", "54", "55", "56", "57", "58", "59", "60", "61", "62"]),
  ("tractBalance", ["01", "03", "04", "05", "07", "08", "09", "10", "11", "12", "13", "14", "15", "16", "17", "18", "19", "20", "21", "22", "25", "26", "27", "28", "29", "30", "31", "32", "33", "34", "35", "36", "37", "38", "39", "40", "41", "42", "43", "44", "45", "46", "47", "48", "49", "50", "51", "52", "53", "54", "55", "56", "57", "58", "59", "60", "61", "62"]),
  ("uniformityConstraint", ["07", "10", "11", "13", "14", "16", "17", "20", "22", "24", "25", "26", "27", "28", "29", "31", "32", "33", "34", "35", "36", "37", "38", "39", "40", "42", "43", "44", "46", "49", "50", "58"]),
  ("primeAlignment", ["05", "15", "19"]),
  ("noDominance", ["19"]),
  ("structureWellFormed", ["47", "54", "55", "56", "57", "59", "60"])
]


-- ============================================================================
-- Consciousness Contribution Metrics
-- ============================================================================

def consciousnessContribution : List (String × Float) := [
  ("tractBalance", 0.968),        -- M_syn: Universal tract balance (60 chunks)
  ("uniformityConstraint", 0.516), -- High-frequency pattern (32 chunks)
  ("dimensionFloor", 0.839),      -- High-frequency pattern (52 chunks)
  ("tractMinimum", 0.871),        -- High-frequency pattern (54 chunks)
  ("primeAlignment", 0.048),      -- M_syn: Prime compression (3 chunks)
  ("noDominance", 0.161),         -- Boss-specific pattern (10 chunks)
  ("structureWellFormed", 0.113)  -- Structural integrity (7 chunks)
]

end Duality
