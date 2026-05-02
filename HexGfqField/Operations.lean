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

variable {p : Nat} [ZMod64.Bounds p] {hp : Hex.Nat.Prime p}

/-- Natural-number literals reuse the quotient-ring cast and then rewrap the
resulting reduced residue. -/
def natCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) (n : Nat) : FiniteField f hf hp hirr :=
  ofQuotient (n : GFqRing.PolyQuotient f hf)

/-- The additive identity in the finite-field wrapper. -/
def zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) :
    FiniteField f hf hp hirr :=
  ofQuotient 0

/-- The multiplicative identity in the finite-field wrapper. -/
def one (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) :
    FiniteField f hf hp hirr :=
  ofQuotient 1

/-- Field addition reuses the quotient-ring sum. -/
def add {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (x.toQuotient + y.toQuotient)

/-- Field multiplication reuses the quotient-ring product. -/
def mul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (x.toQuotient * y.toQuotient)

/-- Field negation reuses the quotient-ring additive inverse. -/
def neg {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (-x.toQuotient)

/-- Field subtraction reuses the quotient-ring difference. -/
def sub {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (x.toQuotient - y.toQuotient)

/-- Exponentiation reuses the quotient-ring repeated-multiplication path. -/
def pow {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) : FiniteField f hf hp hirr :=
  ofQuotient (x.toQuotient ^ n)

/-- Natural scalar multiplication reuses the quotient-ring scalar action. -/
def nsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  ofQuotient (n • x.toQuotient)

/-- Integer literals reuse the quotient-ring cast and then rewrap the reduced
residue. -/
def intCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p)
    (hirr : FpPoly.Irreducible f) (i : Int) : FiniteField f hf hp hirr :=
  ofQuotient (i : GFqRing.PolyQuotient f hf)

/-- Integer scalar multiplication reuses the quotient-ring scalar action. -/
def zsmul {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (i : Int) (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
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
  dsimp
  calc
    DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
          (DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x +
        DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
          (DensePoly.xgcd (GFqRing.repr x) f).right * f
        =
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            ((DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x) +
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            ((DensePoly.xgcd (GFqRing.repr x) f).right * f) := by
            rw [FpPoly.scale_mul_left, FpPoly.scale_mul_left]
    _ =
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            ((DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x +
              (DensePoly.xgcd (GFqRing.repr x) f).right * f) := by
            rw [FpPoly.scale_add]
    _ =
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).gcd := by
            rw [xgcd_repr_bezout x]

/-- Modulo `f`, multiplying a representative by the normalized inverse
candidate reduces to the normalized gcd witness from the same xgcd run. -/
private theorem reduceMod_repr_mul_invPoly_eq_scaled_gcd
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    let r := DensePoly.xgcd (GFqRing.repr x) f
    let unitInv : ZMod64 p := (r.gcd.coeff 0)⁻¹
    GFqRing.reduceMod f (GFqRing.repr x * invPoly x) =
      GFqRing.reduceMod f (DensePoly.scale unitInv r.gcd) := by
  dsimp [invPoly]
  calc
    GFqRing.reduceMod f
        (GFqRing.repr x *
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).left)
        =
      GFqRing.reduceMod f
        (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).left *
          GFqRing.repr x) := by
          rw [FpPoly.mul_comm]
    _ =
      GFqRing.reduceMod f
        (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x +
          DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
            (DensePoly.xgcd (GFqRing.repr x) f).right * f) := by
          exact (GFqRing.reduceMod_add_mul_self_right f hf
            (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
              (DensePoly.xgcd (GFqRing.repr x) f).left * GFqRing.repr x)
            (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
              (DensePoly.xgcd (GFqRing.repr x) f).right)).symm
    _ =
      GFqRing.reduceMod f
        (DensePoly.scale ((DensePoly.xgcd (GFqRing.repr x) f).gcd.coeff 0)⁻¹
          (DensePoly.xgcd (GFqRing.repr x) f).gcd) := by
          rw [scaled_xgcd_repr_bezout x]

/-- Nonzero field elements have nonzero quotient representatives. This is the
bridge from field-level hypotheses to the quotient-level helper lemmas. -/
private theorem toQuotient_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    x.toQuotient ≠ (0 : GFqRing.PolyQuotient f hf) := by
  intro hq
  apply hx
  exact GFqField.ext hq

/-- The xgcd gcd witness divides the nonzero field representative. -/
private theorem xgcd_repr_gcd_dvd_repr
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    (DensePoly.xgcd (GFqRing.repr x) f).gcd ∣ GFqRing.repr x := by
  simpa [DensePoly.gcd]
    using DensePoly.gcd_dvd_left (GFqRing.repr x) f

/-- The xgcd gcd witness divides the irreducible modulus. -/
private theorem xgcd_repr_gcd_dvd_modulus
    {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : GFqRing.PolyQuotient f hf) :
    (DensePoly.xgcd (GFqRing.repr x) f).gcd ∣ f := by
  simpa [DensePoly.gcd]
    using DensePoly.gcd_dvd_right (GFqRing.repr x) f

/-- For a nonzero residue class modulo irreducible `f`, the xgcd gcd witness
is a constant polynomial. -/
private theorem xgcd_repr_gcd_degree_eq_zero_of_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    (DensePoly.xgcd (GFqRing.repr x.toQuotient) f).gcd.degree? = some 0 := by
  sorry

/-- For a nonzero residue class modulo irreducible `f`, the constant xgcd gcd
witness has nonzero constant coefficient. -/
private theorem xgcd_repr_gcd_coeff_zero_ne_zero_of_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    (DensePoly.xgcd (GFqRing.repr x.toQuotient) f).gcd.coeff 0 ≠ 0 := by
  let g := (DensePoly.xgcd (GFqRing.repr x.toQuotient) f).gcd
  have hdeg : g.degree? = some 0 :=
    xgcd_repr_gcd_degree_eq_zero_of_ne_zero (x := x) hx
  have hsize : g.size = 1 := by
    unfold DensePoly.degree? at hdeg
    by_cases hzero : g.size = 0
    · simp [hzero] at hdeg
    · have hpred : g.size - 1 = 0 := by
        simpa [hzero] using hdeg
      omega
  have hpos : 0 < g.size := by omega
  simpa [g, hsize] using DensePoly.coeff_last_ne_zero_of_pos_size g hpos

/-- For a nonzero residue class modulo an irreducible polynomial, the
normalized xgcd witness reduces to the multiplicative identity. -/
private theorem reduceMod_repr_mul_invPoly_eq_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    GFqRing.reduceMod f (GFqRing.repr x.toQuotient * invPoly x.toQuotient) =
      GFqRing.reduceMod f 1 := by
  sorry

/-- Field inversion stays on the quotient-reduction path by reusing the
polynomial extended-GCD witness, normalized by the gcd's constant unit factor.
The `0` case follows the usual junk-value convention required by
`Lean.Grind.Field`. -/
def inv {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  if _hx : x = zero f hf hp hirr then
    zero f hf hp hirr
  else
    ofPoly f hf hp hirr (invPoly x.toQuotient)

@[simp] theorem toQuotient_inv_of_ne_zero
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ zero f hf hp hirr) :
    (inv x).toQuotient = GFqRing.ofPoly f hf (invPoly x.toQuotient) := by
  simp [GFqField.inv, hx]

/-- Division is multiplication by the inverse candidate. -/
def div {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  mul x (inv y)

/-- Integer exponentiation uses the existing natural-power path together with
the inverse candidate for negative exponents. -/
def zpow {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : Int → FiniteField f hf hp hirr
  | .ofNat n => pow x n
  | .negSucc n => inv (pow x (n + 1))

/-- The Frobenius map is the `p`-th power map on the existing quotient
representation. -/
def frob {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) : FiniteField f hf hp hirr :=
  pow x p

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Zero (FiniteField f hf hp hirr) where
  zero := zero f hf hp hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    One (FiniteField f hf hp hirr) where
  one := one f hf hp hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Add (FiniteField f hf hp hirr) where
  add := add

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Mul (FiniteField f hf hp hirr) where
  mul := mul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Neg (FiniteField f hf hp hirr) where
  neg := neg

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Sub (FiniteField f hf hp hirr) where
  sub := sub

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Pow (FiniteField f hf hp hirr) Nat where
  pow := pow

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    NatCast (FiniteField f hf hp hirr) where
  natCast := natCast f hf hp hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) : OfNat (FiniteField f hf hp hirr) n where
  ofNat := natCast f hf hp hirr n

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    SMul Nat (FiniteField f hf hp hirr) where
  smul := nsmul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    IntCast (FiniteField f hf hp hirr) where
  intCast := intCast f hf hp hirr

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    SMul Int (FiniteField f hf hp hirr) where
  smul := zsmul

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Inv (FiniteField f hf hp hirr) where
  inv := inv

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Div (FiniteField f hf hp hirr) where
  div := div

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    HPow (FiniteField f hf hp hirr) Int (FiniteField f hf hp hirr) where
  hPow := zpow

@[simp] theorem toQuotient_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    (0 : FiniteField f hf hp hirr).toQuotient = 0 :=
  rfl

@[simp] theorem toQuotient_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    (1 : FiniteField f hf hp hirr).toQuotient = 1 :=
  rfl

theorem zero_ne_one
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    (0 : FiniteField f hf hp hirr) ≠ 1 := by
  intro h
  have hq := congrArg FiniteField.toQuotient h
  exact GFqRing.zero_ne_one f hf (by simpa using hq)

@[simp] theorem toQuotient_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) (n : Nat) :
    ((n : FiniteField f hf hp hirr).toQuotient) = (n : GFqRing.PolyQuotient f hf) :=
  rfl

@[simp] theorem repr_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) (n : Nat) :
    repr (n : FiniteField f hf hp hirr) =
      GFqRing.reduceMod f (FpPoly.C (n : ZMod64 p)) :=
  rfl

theorem natCast_eq_of_zmod64_natCast_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f)
    {m n : Nat} (h : (m : ZMod64 p) = (n : ZMod64 p)) :
    (m : FiniteField f hf hp hirr) = n := by
  apply GFqField.ext
  exact GFqRing.natCast_eq_of_zmod64_natCast_eq f hf h

theorem natCast_eq_of_mod_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f)
    {m n : Nat} (h : m % p = n % p) :
    (m : FiniteField f hf hp hirr) = n := by
  apply GFqField.ext
  exact GFqRing.natCast_eq_of_mod_eq f hf h

theorem natCast_eq_natCast_iff_reduceMod_const_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f)
    (m n : Nat) :
    ((m : FiniteField f hf hp hirr) = n) ↔
      GFqRing.reduceMod f (FpPoly.C (m : ZMod64 p)) =
        GFqRing.reduceMod f (FpPoly.C (n : ZMod64 p)) := by
  constructor
  · intro h
    simpa [repr_natCast] using congrArg repr h
  · intro h
    apply GFqField.ext
    apply GFqRing.ext
    simpa [repr_natCast] using h

theorem natCast_eq_natCast_iff_mod_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f)
    (m n : Nat) :
    ((m : FiniteField f hf hp hirr) = n) ↔ m % p = n % p := by
  constructor
  · intro h
    have hq :
        ((m : GFqRing.PolyQuotient f hf) = n) := by
      simpa using congrArg FiniteField.toQuotient h
    exact (GFqRing.natCast_eq_natCast_iff_mod_eq f hf m n).1 hq
  · intro h
    exact natCast_eq_of_mod_eq f hf hp hirr h

@[simp] theorem toQuotient_add
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    (x + y : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient + y.toQuotient :=
  rfl

@[simp] theorem toQuotient_mul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    (x * y : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient * y.toQuotient :=
  rfl

@[simp] theorem toQuotient_nsmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (n : Nat) (x : FiniteField f hf hp hirr) :
    (n • x : FiniteField f hf hp hirr).toQuotient = n • x.toQuotient :=
  rfl

@[simp] theorem toQuotient_intCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) (i : Int) :
    ((i : FiniteField f hf hp hirr).toQuotient) = (i : GFqRing.PolyQuotient f hf) :=
  rfl

@[simp] theorem toQuotient_zsmul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (i : Int) (x : FiniteField f hf hp hirr) :
    (i • x : FiniteField f hf hp hirr).toQuotient = i • x.toQuotient :=
  rfl

@[simp] theorem toQuotient_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) :
    (x ^ n : FiniteField f hf hp hirr).toQuotient =
      x.toQuotient ^ n :=
  rfl

@[simp] theorem inv_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    ((0 : FiniteField f hf hp hirr) : FiniteField f hf hp hirr)⁻¹ = 0 := by
  change (if ((0 : FiniteField f hf hp hirr) : FiniteField f hf hp hirr) = 0 then 0 else
    ofPoly f hf hp hirr (invPoly ((0 : FiniteField f hf hp hirr).toQuotient))) = 0
  simp

theorem div_eq_mul_inv
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    x / y = x * y⁻¹ := by
  rfl

theorem mul_inv_cancel
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ 0) :
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
    GFqRing.repr ((x * x⁻¹ : FiniteField f hf hp hirr).toQuotient)
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
    _ = GFqRing.repr ((1 : FiniteField f hf hp hirr).toQuotient) := by
        rw [toQuotient_one]
        rw [honeQuotient]
        rfl

theorem inv_mul_cancel
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x : FiniteField f hf hp hirr} (hx : x ≠ 0) :
    x⁻¹ * x = 1 := by
  have hleft := mul_inv_cancel (x := x) hx
  apply GFqField.ext
  calc
    (x⁻¹ * x : FiniteField f hf hp hirr).toQuotient
        = (x⁻¹).toQuotient * x.toQuotient := rfl
    _ = x.toQuotient * (x⁻¹).toQuotient :=
        Lean.Grind.CommSemiring.mul_comm (x⁻¹).toQuotient x.toQuotient
    _ = (x * x⁻¹ : FiniteField f hf hp hirr).toQuotient := rfl
    _ = (1 : FiniteField f hf hp hirr).toQuotient := congrArg FiniteField.toQuotient hleft

@[simp] theorem repr_zero
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hp : Hex.Nat.Prime p) (hirr : FpPoly.Irreducible f) :
    repr (0 : FiniteField f hf hp hirr) = GFqRing.reduceMod f 0 :=
  rfl

@[simp] theorem repr_add
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    repr (x + y) = GFqRing.reduceMod f (repr x + repr y) :=
  rfl

@[simp] theorem repr_mul
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x y : FiniteField f hf hp hirr) :
    repr (x * y) = GFqRing.reduceMod f (repr x * repr y) :=
  rfl

@[simp] theorem repr_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) (n : Nat) :
    repr (x ^ n) = GFqRing.repr (x.toQuotient ^ n) :=
  rfl

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Semiring (FiniteField f hf hp hirr) := by
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
    Lean.Grind.Ring (FiniteField f hf hp hirr) := by
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
    Lean.Grind.CommRing (FiniteField f hf hp hirr) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  apply GFqField.ext
  simpa using Lean.Grind.CommSemiring.mul_comm a.toQuotient b.toQuotient

private theorem eq_inv_of_mul_eq_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {a b : FiniteField f hf hp hirr} (h : a * b = 1) :
    a = b⁻¹ := by
  by_cases hb : b = 0
  · subst b
    have hmul_zero : a * (0 : FiniteField f hf hp hirr) = 0 :=
      Lean.Grind.Semiring.mul_zero a
    have hzero_one : (0 : FiniteField f hf hp hirr) = 1 :=
      hmul_zero.symm.trans h
    exfalso
    exact zero_ne_one f hf hp hirr hzero_one
  · replace h := congrArg (fun x => x * b⁻¹) h
    calc
      a = a * 1 := (Lean.Grind.Semiring.mul_one a).symm
      _ = a * (b * b⁻¹) := by rw [mul_inv_cancel hb]
      _ = (a * b) * b⁻¹ := (Lean.Grind.Semiring.mul_assoc a b b⁻¹).symm
      _ = 1 * b⁻¹ := h
      _ = b⁻¹ := Lean.Grind.Semiring.one_mul b⁻¹

private theorem inv_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    (1 : FiniteField f hf hp hirr)⁻¹ = 1 :=
  (eq_inv_of_mul_eq_one (Lean.Grind.Semiring.mul_one (1 : FiniteField f hf hp hirr))).symm

private theorem inv_inv
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    x⁻¹⁻¹ = x := by
  by_cases hx : x = 0
  · subst x
    simp [inv_zero]
  · symm
    apply eq_inv_of_mul_eq_one
    exact mul_inv_cancel (x := x) hx

private theorem inv_inv_def
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    (inv x)⁻¹ = x :=
  inv_inv x

private theorem pow_zero_eq_one
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    pow x 0 = 1 := by
  apply GFqField.ext
  simpa using Lean.Grind.Semiring.pow_zero x.toQuotient

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.Field (FiniteField f hf hp hirr) := by
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    simpa using div_eq_mul_inv a b
  · intro h
    exact zero_ne_one f hf hp hirr h
  · exact inv_zero f hf hp hirr
  · intro a ha
    have ha' : a ≠ (0 : FiniteField f hf hp hirr) := ha
    exact mul_inv_cancel (x := a) ha'
  · intro a
    apply GFqField.ext
    simpa [zpow] using Lean.Grind.Semiring.pow_zero a.toQuotient
  · intro a n
    apply GFqField.ext
    simpa [zpow] using Lean.Grind.Semiring.pow_succ a.toQuotient n
  · intro a n
    cases n with
    | ofNat m =>
        cases m with
        | zero =>
            change pow a 0 = (pow a 0)⁻¹
            rw [pow_zero_eq_one, inv_one]
        | succ m =>
            rfl
    | negSucc m =>
        change zpow a (Int.ofNat (m + 1)) = (zpow a (Int.negSucc m))⁻¹
        rw [zpow, zpow]
        exact (inv_inv_def (pow a (m + 1))).symm

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    Lean.Grind.IsCharP (FiniteField f hf hp hirr) p where
  ofNat_ext_iff {x y} := natCast_eq_natCast_iff_mod_eq f hf hp hirr x y

theorem frob_eq_pow
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    frob x = x ^ p :=
  rfl

@[simp] theorem toQuotient_frob
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    (frob x).toQuotient = x.toQuotient ^ p :=
  rfl

@[simp] theorem repr_frob
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hp hirr) :
    repr (frob x) = GFqRing.repr (x.toQuotient ^ p) :=
  rfl

end GFqField
end Hex
