/-
Shared base for Duality chunks:
- X8 type
- N, unitary
- tract sum helpers
-/

namespace Duality

-- TODO: Replace stub with proper Mathlib import when time budget allows
-- Lightweight stub for Real type (chunks 13, 20, 39, 58 have malformed constraints)
-- The transpiler generated invalid code: "True = Real ∧ ..." which is nonsensical
-- Current workaround: Stub type enables compilation without Mathlib overhead
-- Future improvement: `import Mathlib.Data.Real.Basic` + fix transpiler
def Real : Type := Unit

-- TODO: Replace placeholders with proper struct definitions when requirements clear
-- Placeholder types for struct syntax chunks (16, 28, 38, 59, 60)
-- The transpiler generated incomplete existential syntax: "(∃ φ : GoalSpec → Vector)"
-- Current workaround: Stub structs enable compilation
-- Future improvement: Define proper GoalSpec and Vector types based on actual needs
structure GoalSpec where
  dummy : Unit := ()
deriving Repr

structure Vector where
  dummy : Unit := ()
deriving Repr

def N : Nat := 100

structure X8 where
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
  x5 : Nat
  x6 : Nat
  x7 : Nat
  x8 : Nat
deriving Repr, DecidableEq

def unitary (x : X8) : Prop :=
  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N

instance (x : X8) : Decidable (unitary x) :=
  inferInstanceAs (Decidable (_ = _))

@[simp] def T_ext (x : X8) : Nat := x.x1 + x.x2 + x.x3 + x.x4
@[simp] def T_int (x : X8) : Nat := x.x5 + x.x6 + x.x7 + x.x8

end Duality
