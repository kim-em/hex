import HexModArith
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.ZMod.Defs

/-!
Bridge scaffolding between `HexModArith.ZMod64 p` and Mathlib's `ZMod p`.

This module packages the concrete conversion pair between Hex's
`UInt64`-backed residue representation and Mathlib's canonical `ZMod p`,
then states the scaffolded ring-equivalence and transport lemmas that
downstream bridge libraries will use to move between executable modular
computation and Mathlib theorem statements.
-/

namespace HexModArithMathlib

open HexModArith

namespace ZMod64

variable {p : Nat} [NeZero p]

/-- A nonzero modulus is positive. -/
private theorem modulus_pos : 0 < p :=
  Nat.pos_of_ne_zero (NeZero.ne p)

/-- Convert an executable `ZMod64 p` residue into Mathlib's `ZMod p`. -/
def toZMod (a : HexModArith.ZMod64 p) : ZMod p :=
  a.toNat

/-- The canonical natural-number representative of a Mathlib `ZMod p` residue. -/
def representative (a : ZMod p) : Nat := by
  cases p with
  | zero =>
      exact False.elim (NeZero.ne 0 rfl)
  | succ n =>
      exact (show Fin (n + 1) from a).val

/-- The canonical representative stays below the modulus. -/
theorem representative_lt (a : ZMod p) : representative a < p := by
  cases p with
  | zero =>
      exact False.elim (NeZero.ne 0 rfl)
  | succ n =>
      exact (show Fin (n + 1) from a).isLt

/-- Convert a Mathlib `ZMod p` residue into the executable `ZMod64 p` form. -/
def ofZMod (a : ZMod p) : HexModArith.ZMod64 p :=
  HexModArith.ZMod64.ofNat p (representative a) modulus_pos

/-- The executable and Mathlib modular representations are intended to agree. -/
def equiv : RingEquiv (HexModArith.ZMod64 p) (ZMod p) where
  toFun := toZMod
  invFun := ofZMod
  left_inv := by
    intro a
    sorry
  right_inv := by
    intro a
    sorry
  map_mul' := by
    intro a b
    sorry
  map_add' := by
    intro a b
    sorry

/-- Converting an executable residue to Mathlib and back is the identity. -/
theorem ofZMod_toZMod (a : HexModArith.ZMod64 p) :
    ofZMod (toZMod a) = a := by
  exact equiv.left_inv a

/-- Converting a Mathlib residue to the executable form and back is the identity. -/
theorem toZMod_ofZMod (a : ZMod p) :
    toZMod (ofZMod a) = a := by
  exact equiv.right_inv a

/-- The executable `toNat` view matches the chosen Mathlib-side representative. -/
@[simp] theorem representative_toZMod (a : HexModArith.ZMod64 p) :
    representative (toZMod a) = a.toNat := by
  sorry

/-- The executable representative extracted from `ofZMod` is the chosen Mathlib representative. -/
@[simp] theorem toNat_ofZMod (a : ZMod p) :
    (ofZMod a).toNat = representative a := by
  sorry

/-- Natural-number casts are preserved by the bridge into Mathlib's `ZMod`. -/
@[simp] theorem toZMod_natCast (n : Nat) :
    toZMod (n : HexModArith.ZMod64 p) = (n : ZMod p) := by
  sorry

/-- Integer casts are preserved by the bridge into Mathlib's `ZMod`. -/
@[simp] theorem toZMod_intCast (z : Int) :
    toZMod (z : HexModArith.ZMod64 p) = (z : ZMod p) := by
  sorry

/-- The bridge respects the executable representative map into `Nat`. -/
theorem toNat_eq_val (a : HexModArith.ZMod64 p) :
    a.toNat = representative (toZMod a) := by
  exact (representative_toZMod a).symm

end ZMod64

end HexModArithMathlib
