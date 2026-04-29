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

/-- Normalize an extended-GCD witness by the gcd's constant-unit factor so the
left coefficient becomes a genuine inverse candidate modulo `f`. -/
private def invPoly {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) : FpPoly p :=
  let r := DensePoly.xgcd (GFqRing.repr x) f
  let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
  DensePoly.scale unitInv r.left

/-- The inverse candidate is the normalized left Bezout coefficient from the
extended gcd between the representative and the modulus. -/
private theorem invPoly_eq_scale_xgcd_left
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    invPoly x =
      let r := DensePoly.xgcd (GFqRing.repr x) f
      let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
      DensePoly.scale unitInv r.left := by
  rfl

/-- The extended-gcd output gives the unscaled Bezout identity for the reduced
representative and the modulus. -/
private theorem xgcd_repr_bezout
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    let r := DensePoly.xgcd (GFqRing.repr x) f
    r.left * GFqRing.repr x + r.right * f = r.gcd := by
  simpa using DensePoly.xgcd_bezout (GFqRing.repr x) f

/-- After scaling the Bezout coefficients by the inverse of the gcd's constant
term, the left coefficient is still a quotient-level inverse candidate. -/
private theorem scaled_xgcd_repr_bezout
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    let r := DensePoly.xgcd (GFqRing.repr x) f
    let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
    DensePoly.scale unitInv r.left * GFqRing.repr x +
        DensePoly.scale unitInv r.right * f =
      DensePoly.scale unitInv r.gcd := by
  sorry

/-- Modulo `f`, multiplying a representative by the normalized inverse
candidate reduces to the normalized gcd witness from the same xgcd run. -/
private theorem reduceMod_repr_mul_invPoly_eq_scaled_gcd
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    let r := DensePoly.xgcd (GFqRing.repr x) f
    let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
    GFqRing.reduceMod f (GFqRing.repr x * invPoly x) =
      GFqRing.reduceMod f (DensePoly.scale unitInv r.gcd) := by
  sorry

/-- Nonzero field elements have nonzero quotient representatives. This is the
bridge from field-level hypotheses to the quotient-level helper lemmas. -/
private theorem toQuotient_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hirr} (hx : x ≠ zero f hf hirr) :
    x.toQuotient ≠ (0 : GFqRing.PolyQuotient f hf) := by
  intro hq
  apply hx
  exact GFqField.ext hq

/-- For a nonzero residue class modulo an irreducible polynomial, the
normalized xgcd witness reduces to the multiplicative identity. -/
private theorem reduceMod_repr_mul_invPoly_eq_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hirr} (hx : x ≠ zero f hf hirr) :
    GFqRing.reduceMod f (GFqRing.repr x.toQuotient * invPoly x.toQuotient) =
      GFqRing.reduceMod f 1 := by
  sorry

/-- Field inversion stays on the quotient-reduction path by reusing the
polynomial extended-GCD witness, normalized by the gcd's constant unit factor.
The `0` case follows the usual junk-value convention required by
`Lean.Grind.Field`. -/
def inv {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) : FiniteField f hf hirr :=
  if _hx : x = zero f hf hirr then
    zero f hf hirr
  else
    ofPoly f hf hirr (invPoly x.toQuotient)

@[simp] theorem toQuotient_inv_of_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hirr} (hx : x ≠ zero f hf hirr) :
    (inv x).toQuotient = GFqRing.ofPoly f hf (invPoly x.toQuotient) := by
  simp [GFqField.inv, hx]

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

theorem zero_ne_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) :
    (0 : FiniteField f hf hirr) ≠ 1 := by
  intro h
  have hq := congrArg FiniteField.toQuotient h
  exact GFqRing.zero_ne_one f hf (by simpa using hq)

@[simp] theorem toQuotient_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) (n : Nat) :
    ((n : FiniteField f hf hirr).toQuotient) = (n : GFqRing.PolyQuotient f hf) :=
  rfl

@[simp] theorem repr_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) (n : Nat) :
    repr (n : FiniteField f hf hirr) =
      GFqRing.reduceMod f (FpPoly.C (n : ZMod64 p)) :=
  rfl

theorem natCast_eq_of_zmod64_natCast_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f)
    {m n : Nat} (h : (m : ZMod64 p) = (n : ZMod64 p)) :
    (m : FiniteField f hf hirr) = n := by
  apply GFqField.ext
  exact GFqRing.natCast_eq_of_zmod64_natCast_eq f hf h

theorem natCast_eq_of_mod_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f)
    {m n : Nat} (h : m % p = n % p) :
    (m : FiniteField f hf hirr) = n := by
  apply GFqField.ext
  exact GFqRing.natCast_eq_of_mod_eq f hf h

theorem natCast_eq_natCast_iff_reduceMod_const_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f)
    (m n : Nat) :
    ((m : FiniteField f hf hirr) = n) ↔
      GFqRing.reduceMod f (FpPoly.C (m : ZMod64 p)) =
        GFqRing.reduceMod f (FpPoly.C (n : ZMod64 p)) := by
  constructor
  · intro h
    simpa [repr_natCast] using congrArg repr h
  · intro h
    apply GFqField.ext
    apply GFqRing.ext
    simpa [repr_natCast] using h

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
  change (if ((0 : FiniteField f hf hirr) : FiniteField f hf hirr) = 0 then 0 else
    ofPoly f hf hirr (invPoly ((0 : FiniteField f hf hirr).toQuotient))) = 0
  simp

theorem div_eq_mul_inv
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hirr) :
    x / y = x * y⁻¹ := by
  rfl

theorem mul_inv_cancel
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hirr} (hx : x ≠ 0) :
    x * x⁻¹ = 1 := by
  have hreduced := reduceMod_repr_mul_invPoly_eq_one (x := x) hx
  have hxrepr :
      GFqRing.reduceMod f (GFqRing.repr x.toQuotient) = GFqRing.repr x.toQuotient := by
    rcases x.toQuotient.property with ⟨g, hg⟩
    change GFqRing.reduceMod f x.toQuotient.val = x.toQuotient.val
    rw [hg, GFqRing.reduceMod_idem]
  have hinv := toQuotient_inv_of_ne_zero (x := x) hx
  have honeQuotient :
      (1 : GFqRing.PolyQuotient f hf) = GFqRing.one f hf := by
    change GFqRing.natCast f hf 1 = GFqRing.one f hf
    rfl
  have hmulReduce :
      GFqRing.reduceMod f
          (GFqRing.repr x.toQuotient * GFqRing.reduceMod f (invPoly x.toQuotient)) =
        GFqRing.reduceMod f (GFqRing.repr x.toQuotient * invPoly x.toQuotient) := by
    simpa [hxrepr] using
      (GFqRing.reduceMod_mul_reduceMod f (GFqRing.repr x.toQuotient)
        (invPoly x.toQuotient)).symm
  apply GFqField.ext
  apply GFqRing.ext
  calc
    GFqRing.repr ((x * x⁻¹ : FiniteField f hf hirr).toQuotient)
        = GFqRing.repr (x.toQuotient * GFqRing.ofPoly f hf (invPoly x.toQuotient)) := by
            rw [toQuotient_mul]
            change GFqRing.repr (x.toQuotient * (inv x).toQuotient) =
              GFqRing.repr (x.toQuotient * GFqRing.ofPoly f hf (invPoly x.toQuotient))
            rw [hinv]
    _ = GFqRing.reduceMod f
            (GFqRing.repr x.toQuotient * GFqRing.reduceMod f (invPoly x.toQuotient)) := by
            rfl
    _ = GFqRing.reduceMod f (GFqRing.repr x.toQuotient * invPoly x.toQuotient) :=
        hmulReduce
    _ = GFqRing.reduceMod f 1 := hreduced
    _ = GFqRing.repr ((1 : FiniteField f hf hirr).toQuotient) := by
        rw [toQuotient_one]
        rw [honeQuotient]
        rfl

theorem inv_mul_cancel
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hirr} (hx : x ≠ 0) :
    x⁻¹ * x = 1 := by
  have hleft := mul_inv_cancel (x := x) hx
  apply GFqField.ext
  calc
    (x⁻¹ * x : FiniteField f hf hirr).toQuotient
        = (x⁻¹).toQuotient * x.toQuotient := rfl
    _ = x.toQuotient * (x⁻¹).toQuotient :=
        Lean.Grind.CommSemiring.mul_comm (x⁻¹).toQuotient x.toQuotient
    _ = (x * x⁻¹ : FiniteField f hf hirr).toQuotient := rfl
    _ = (1 : FiniteField f hf hirr).toQuotient := congrArg FiniteField.toQuotient hleft

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
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.add_zero a.toQuotient
  · intro a b
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.add_comm a.toQuotient b.toQuotient
  · intro a b c
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.add_assoc a.toQuotient b.toQuotient c.toQuotient
  · intro a b c
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.mul_assoc a.toQuotient b.toQuotient c.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.mul_one a.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.one_mul a.toQuotient
  · intro a b c
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.left_distrib a.toQuotient b.toQuotient c.toQuotient
  · intro a b c
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.right_distrib a.toQuotient b.toQuotient c.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.zero_mul a.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.mul_zero a.toQuotient
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.pow_zero a.toQuotient
  · intro a n
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.pow_succ a.toQuotient n
  · intro n
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.ofNat_succ (α := GFqRing.PolyQuotient f hf) n
  · intro n
    apply GFqField.ext
    simpa using Lean.Grind.Semiring.ofNat_eq_natCast (α := GFqRing.PolyQuotient f hf) n
  · intro n a
    apply GFqField.ext
    simpa using
      Lean.Grind.Semiring.nsmul_eq_natCast_mul (α := GFqRing.PolyQuotient f hf) n a.toQuotient

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Ring (FiniteField f hf hirr) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply GFqField.ext
    simpa using Lean.Grind.Ring.neg_add_cancel a.toQuotient
  · intro a b
    apply GFqField.ext
    simpa using Lean.Grind.Ring.sub_eq_add_neg a.toQuotient b.toQuotient
  · intro i a
    apply GFqField.ext
    simpa using Lean.Grind.Ring.neg_zsmul i a.toQuotient
  · intro n a
    apply GFqField.ext
    simpa using Lean.Grind.Ring.zsmul_natCast_eq_nsmul (α := GFqRing.PolyQuotient f hf) n a.toQuotient
  · intro n
    apply GFqField.ext
    simpa using Lean.Grind.Ring.intCast_ofNat (α := GFqRing.PolyQuotient f hf) n
  · intro i
    apply GFqField.ext
    simpa using Lean.Grind.Ring.intCast_neg (α := GFqRing.PolyQuotient f hf) i

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.CommRing (FiniteField f hf hirr) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  apply GFqField.ext
  simpa using Lean.Grind.CommSemiring.mul_comm a.toQuotient b.toQuotient

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Field (FiniteField f hf hirr) := by
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    simpa using div_eq_mul_inv a b
  · intro h
    exact zero_ne_one f hf hirr h
  · exact inv_zero f hf hirr
  · intro a ha
    have ha' : a ≠ (0 : FiniteField f hf hirr) := ha
    exact mul_inv_cancel (x := a) ha'
  · intro a
    apply GFqField.ext
    simpa [zpow] using Lean.Grind.Semiring.pow_zero a.toQuotient
  · intro a n
    apply GFqField.ext
    simpa [zpow] using Lean.Grind.Semiring.pow_succ a.toQuotient n
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
