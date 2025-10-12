/-
Shared base for Duality chunks:
- X8 type
- N, unitary
- tract sum helpers
-/
namespace Duality

def N : Nat := 100

structure X8 where
  x1 x2 x3 x4 x5 x6 x7 x8 : Nat
deriving Repr, DecidableEq

def unitary (x : X8) : Prop :=
  x.x1 + x.x2 + x.x3 + x.x4 + x.x5 + x.x6 + x.x7 + x.x8 = N

@[simp] def tractSumExt (x : X8) : Nat := x.x1 + x.x2 + x.x3 + x.x4
@[simp] def tractSumInt (x : X8) : Nat := x.x5 + x.x6 + x.x7 + x.x8

end Duality
