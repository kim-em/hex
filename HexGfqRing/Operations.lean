import Init.Grind.Ring.Basic
import HexGfqRing.Basic

/-!
Executable quotient-ring operations for canonical representatives in `F_p[x] / (f)`.

This module extends the basic quotient wrapper with normalized addition,
multiplication, negation, subtraction, exponentiation, and the algebra-instance
surface needed by downstream finite-field layers.
-/
namespace Hex

namespace GFqRing

variable {p : Nat} [ZMod64.Bounds p]

/-- Coefficientwise additive inverse on `F_p[x]`. -/
private def negPoly (g : FpPoly p) : FpPoly p :=
  DensePoly.ofCoeffs <|
    (List.range g.size).map (fun i => (0 : ZMod64 p) - g.coeff i) |>.toArray

/-- The quotient zero element. -/
def zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) : PolyQuotient f hf :=
  ofPoly f hf 0

/-- The quotient one element. -/
def one (f : FpPoly p) (hf : 0 < FpPoly.degree f) : PolyQuotient f hf :=
  ofPoly f hf 1

/-- Quotient addition reduces the sum of representatives. -/
def add {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (repr x + repr y)

/-- Quotient multiplication reduces the product of representatives. -/
def mul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (repr x * repr y)

/-- Quotient negation reduces the coefficientwise additive inverse. -/
def neg {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (negPoly (repr x))

/-- Quotient subtraction reduces the difference of representatives. -/
def sub {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (repr x - repr y)

/-- Quotient exponentiation by repeated multiplication. -/
def pow {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) : Nat → PolyQuotient f hf
  | 0 => one f hf
  | n + 1 => mul (pow x n) x

/-- Natural-number literals in the quotient ring. -/
def natCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) : Nat → PolyQuotient f hf
  | 0 => zero f hf
  | n + 1 => add (natCast f hf n) (one f hf)

/-- Natural scalar multiplication in the quotient ring. -/
def nsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (n : Nat) (x : PolyQuotient f hf) : PolyQuotient f hf :=
  Nat.rec (zero f hf) (fun _ acc => add acc x) n

/-- Integer literals in the quotient ring. -/
def intCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) : Int → PolyQuotient f hf
  | .ofNat n => natCast f hf n
  | .negSucc n => neg (natCast f hf (n + 1))

/-- Integer scalar multiplication in the quotient ring. -/
def zsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (i : Int) (x : PolyQuotient f hf) : PolyQuotient f hf :=
  match i with
  | .ofNat n => nsmul n x
  | .negSucc n => neg (nsmul (n + 1) x)

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Zero (PolyQuotient f hf) where
  zero := zero f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : One (PolyQuotient f hf) where
  one := one f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Add (PolyQuotient f hf) where
  add := add

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Mul (PolyQuotient f hf) where
  mul := mul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Neg (PolyQuotient f hf) where
  neg := neg

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Sub (PolyQuotient f hf) where
  sub := sub

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Pow (PolyQuotient f hf) Nat where
  pow := pow

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : NatCast (PolyQuotient f hf) where
  natCast := natCast f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} (n : Nat) :
    OfNat (PolyQuotient f hf) n where
  ofNat := natCast f hf n

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : SMul Nat (PolyQuotient f hf) where
  smul := nsmul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : IntCast (PolyQuotient f hf) where
  intCast := intCast f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : SMul Int (PolyQuotient f hf) where
  smul := zsmul

@[simp] theorem repr_zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    repr (0 : PolyQuotient f hf) = reduceMod f 0 :=
  rfl

@[simp] theorem repr_add {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    repr (x + y) = reduceMod f (repr x + repr y) :=
  rfl

@[simp] theorem repr_mul {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    repr (x * y) = reduceMod f (repr x * repr y) :=
  rfl

@[simp] theorem repr_neg {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    repr (-x) = reduceMod f (negPoly (repr x)) :=
  rfl

@[simp] theorem repr_sub {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) :
    repr (x - y) = reduceMod f (repr x - repr y) :=
  rfl

@[simp] theorem repr_pow {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) :
    repr (x ^ n) = repr (pow x n) :=
  rfl

theorem reduceMod_add_reduceMod (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (a + b) = reduceMod f (reduceMod f a + reduceMod f b) := by
  sorry

theorem reduceMod_mul_reduceMod (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (a * b) = reduceMod f (reduceMod f a * reduceMod f b) := by
  sorry

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Lean.Grind.Semiring (PolyQuotient f hf) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    sorry
  · intro a b
    apply Subtype.ext
    sorry
  · intro a b c
    apply Subtype.ext
    sorry
  · intro a b c
    apply Subtype.ext
    sorry
  · intro a
    apply Subtype.ext
    sorry
  · intro a
    apply Subtype.ext
    sorry
  · intro a b c
    apply Subtype.ext
    sorry
  · intro a b c
    apply Subtype.ext
    sorry
  · intro a
    apply Subtype.ext
    sorry
  · intro a
    apply Subtype.ext
    sorry
  · intro a
    apply Subtype.ext
    sorry
  · intro a n
    apply Subtype.ext
    sorry
  · intro n
    sorry
  · intro n
    sorry
  · intro n a
    sorry

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Lean.Grind.Ring (PolyQuotient f hf) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply Subtype.ext
    sorry
  · intro a b
    apply Subtype.ext
    sorry
  · intro i a
    apply Subtype.ext
    sorry
  · intro n a
    sorry
  · intro n
    sorry
  · intro i
    sorry

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : Lean.Grind.CommRing (PolyQuotient f hf) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  apply Subtype.ext
  sorry

end GFqRing

end Hex
