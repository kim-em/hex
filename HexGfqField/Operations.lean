import Init.Grind.Ring.Field
import HexGfqField.Basic

/-!
Executable finite-field operations for `F_p[x] / (f)`.

This module keeps `GFqField.FiniteField` on the quotient-ring arithmetic path:
all operations, exponentiation, and Frobenius are implemented by delegating to
`Hex.GFqRing.PolyQuotient` and then rewrapping the reduced representative.
-/
namespace Hex

namespace GFqField

variable {p : Nat} [ZMod64.Bounds p]

/-- Natural-number literals reuse the quotient-ring cast and then rewrap the
resulting reduced residue. -/
def natCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f)
    (n : Nat) : FiniteField f hf hirr :=
  ofQuotient (n : GFqRing.PolyQuotient f hf)

/-- The additive identity in the finite-field wrapper. -/
def zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    FiniteField f hf hirr :=
  ofQuotient 0

/-- The multiplicative identity in the finite-field wrapper. -/
def one (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    FiniteField f hf hirr :=
  ofQuotient 1

/-- Field addition reuses the quotient-ring sum. -/
def add {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) : FiniteField f hf hirr :=
  ofQuotient (x.toQuotient + y.toQuotient)

/-- Field multiplication reuses the quotient-ring product. -/
def mul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) : FiniteField f hf hirr :=
  ofQuotient (x.toQuotient * y.toQuotient)

/-- Field negation reuses the quotient-ring additive inverse. -/
def neg {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) : FiniteField f hf hirr :=
  ofQuotient (-x.toQuotient)

/-- Field subtraction reuses the quotient-ring difference. -/
def sub {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) : FiniteField f hf hirr :=
  ofQuotient (x.toQuotient - y.toQuotient)

/-- Exponentiation reuses the quotient-ring repeated-multiplication path. -/
def pow {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) (n : Nat) : FiniteField f hf hirr :=
  ofQuotient (x.toQuotient ^ n)

/-- Natural scalar multiplication reuses the quotient-ring scalar action. -/
def nsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) (x : FiniteField f hf hirr) : FiniteField f hf hirr :=
  ofQuotient (n • x.toQuotient)

/-- Integer literals reuse the quotient-ring cast and then rewrap the reduced
residue. -/
def intCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f)
    (i : Int) : FiniteField f hf hirr :=
  ofQuotient (i : GFqRing.PolyQuotient f hf)

/-- Integer scalar multiplication reuses the quotient-ring scalar action. -/
def zsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (i : Int) (x : FiniteField f hf hirr) : FiniteField f hf hirr :=
  ofQuotient (i • x.toQuotient)

/-- The extended-GCD left coefficient is the executable inverse candidate for a
nonzero residue class modulo an irreducible polynomial. -/
private def invPoly {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) : FpPoly p :=
  (DensePoly.xgcd (GFqRing.repr x) f).left

/-- Field inversion stays on the quotient-reduction path by reusing the
polynomial extended-GCD witness. The `0` case follows the usual junk-value
convention required by `Lean.Grind.Field`. -/
def inv {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) : FiniteField f hf hirr :=
  if _hx : x = zero f hf hirr then
    zero f hf hirr
  else
    ofPoly f hf hirr (invPoly x.toQuotient)

/-- Division is multiplication by the inverse candidate. -/
def div {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) : FiniteField f hf hirr :=
  mul x (inv y)

/-- Integer exponentiation uses the existing natural-power path together with
the inverse candidate for negative exponents. -/
def zpow {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) : Int → FiniteField f hf hirr
  | .ofNat n => pow x n
  | .negSucc n => inv (pow x (n + 1))

/-- The Frobenius map is the `p`-th power map on the existing quotient
representation. -/
def frob {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) : FiniteField f hf hirr :=
  pow x p

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Zero (FiniteField f hf hirr) where
  zero := zero f hf hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    One (FiniteField f hf hirr) where
  one := one f hf hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Add (FiniteField f hf hirr) where
  add := add

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Mul (FiniteField f hf hirr) where
  mul := mul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Neg (FiniteField f hf hirr) where
  neg := neg

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Sub (FiniteField f hf hirr) where
  sub := sub

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Pow (FiniteField f hf hirr) Nat where
  pow := pow

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    NatCast (FiniteField f hf hirr) where
  natCast := natCast f hf hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) : OfNat (FiniteField f hf hirr) n where
  ofNat := natCast f hf hirr n

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    SMul Nat (FiniteField f hf hirr) where
  smul := nsmul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    IntCast (FiniteField f hf hirr) where
  intCast := intCast f hf hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    SMul Int (FiniteField f hf hirr) where
  smul := zsmul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Inv (FiniteField f hf hirr) where
  inv := inv

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Div (FiniteField f hf hirr) where
  div := div

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    HPow (FiniteField f hf hirr) Int (FiniteField f hf hirr) where
  hPow := zpow

@[simp] theorem toQuotient_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    (0 : FiniteField f hf hirr).toQuotient = 0 :=
  rfl

@[simp] theorem toQuotient_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    (1 : FiniteField f hf hirr).toQuotient = 1 :=
  rfl

@[simp] theorem toQuotient_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) (n : Nat) :
    ((n : FiniteField f hf hirr).toQuotient) = (n : GFqRing.PolyQuotient f hf) :=
  rfl

@[simp] theorem toQuotient_add
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) :
    (x + y : FiniteField f hf hirr).toQuotient =
      x.toQuotient + y.toQuotient :=
  rfl

@[simp] theorem toQuotient_mul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) :
    (x * y : FiniteField f hf hirr).toQuotient =
      x.toQuotient * y.toQuotient :=
  rfl

@[simp] theorem toQuotient_nsmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) (x : FiniteField f hf hirr) :
    (n • x : FiniteField f hf hirr).toQuotient = n • x.toQuotient :=
  rfl

@[simp] theorem toQuotient_intCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) (i : Int) :
    ((i : FiniteField f hf hirr).toQuotient) = (i : GFqRing.PolyQuotient f hf) :=
  rfl

@[simp] theorem toQuotient_zsmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (i : Int) (x : FiniteField f hf hirr) :
    (i • x : FiniteField f hf hirr).toQuotient = i • x.toQuotient :=
  rfl

@[simp] theorem toQuotient_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) (n : Nat) :
    (x ^ n : FiniteField f hf hirr).toQuotient =
      x.toQuotient ^ n :=
  rfl

@[simp] theorem inv_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    ((0 : FiniteField f hf hirr) : FiniteField f hf hirr)⁻¹ = 0 := by
  sorry

theorem div_eq_mul_inv
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) :
    x / y = x * y⁻¹ := by
  sorry

theorem mul_inv_cancel
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hirr} (hx : x ≠ 0) :
    x * x⁻¹ = 1 := by
  sorry

theorem inv_mul_cancel
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hirr} (hx : x ≠ 0) :
    x⁻¹ * x = 1 := by
  sorry

@[simp] theorem repr_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    repr (0 : FiniteField f hf hirr) = GFqRing.reduceMod f 0 :=
  rfl

@[simp] theorem repr_add
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) :
    repr (x + y) = GFqRing.reduceMod f (repr x + repr y) :=
  rfl

@[simp] theorem repr_mul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) :
    repr (x * y) = GFqRing.reduceMod f (repr x * repr y) :=
  rfl

@[simp] theorem repr_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) (n : Nat) :
    repr (x ^ n) = GFqRing.repr (x.toQuotient ^ n) :=
  rfl

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Semiring (FiniteField f hf hirr) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    ext
    sorry
  · intro a b
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a n
    ext
    sorry
  · intro n
    ext
    sorry
  · intro n
    ext
    sorry
  · intro n a
    ext
    sorry

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Ring (FiniteField f hf hirr) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    ext
    sorry
  · intro a b
    ext
    sorry
  · intro i a
    ext
    sorry
  · intro n a
    ext
    sorry
  · intro n
    ext
    sorry
  · intro i
    ext
    sorry

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.CommRing (FiniteField f hf hirr) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  ext
  sorry

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Field (FiniteField f hf hirr) := by
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    exact div_eq_mul_inv a b
  · intro h
    sorry
  · simp [inv_zero]
  · intro a ha
    exact mul_inv_cancel (x := a) ha
  · intro a
    ext
    sorry
  · intro a n
    ext
    sorry
  · intro a n
    ext
    sorry

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.IsCharP (FiniteField f hf hirr) p where
  ofNat_ext_iff {x y} := by
    constructor
    · intro h
      sorry
    · intro h
      ext
      sorry

theorem frob_eq_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) :
    frob x = x ^ p :=
  rfl

@[simp] theorem toQuotient_frob
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) :
    (frob x).toQuotient = x.toQuotient ^ p :=
  rfl

@[simp] theorem repr_frob
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) :
    repr (frob x) = GFqRing.repr (x.toQuotient ^ p) :=
  rfl

end GFqField
end Hex
