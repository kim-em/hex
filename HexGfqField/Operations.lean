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

@[simp] theorem toQuotient_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    (0 : FiniteField f hf hirr).toQuotient = 0 :=
  rfl

@[simp] theorem toQuotient_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    (1 : FiniteField f hf hirr).toQuotient = 1 :=
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

@[simp] theorem toQuotient_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) (n : Nat) :
    (x ^ n : FiniteField f hf hirr).toQuotient =
      x.toQuotient ^ n :=
  rfl

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
