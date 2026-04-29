import Init.Grind.Ring.Basic
import HexModArith.Ring
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

/-- The quotient zero element. -/
def zero (f : FpPoly p) (hf : 0 < FpPoly.degree f) : PolyQuotient f hf :=
  ofPoly f hf 0

/-- The quotient one element. -/
def one (f : FpPoly p) (hf : 0 < FpPoly.degree f) : PolyQuotient f hf :=
  ofPoly f hf 1

/-- Embed a prime-field constant as a quotient-ring constant polynomial. -/
def const (f : FpPoly p) (hf : 0 < FpPoly.degree f) (c : ZMod64 p) :
    PolyQuotient f hf :=
  ofPoly f hf (FpPoly.C c)

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
  ofPoly f hf (-repr x)

/-- Quotient subtraction reduces the difference of representatives. -/
def sub {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x y : PolyQuotient f hf) : PolyQuotient f hf :=
  ofPoly f hf (repr x - repr y)

/-- Quotient exponentiation uses square-and-multiply on the exponent bits. -/
def pow {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) (n : Nat) : PolyQuotient f hf :=
  let rec go (acc base : PolyQuotient f hf) (k : Nat) : PolyQuotient f hf :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then mul acc base else acc
      go acc' (mul base base) (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go (one f hf) x n

/-- Natural-number literals in the quotient ring are reduced constant polynomials. -/
def natCast (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) : PolyQuotient f hf :=
  const f hf (n : ZMod64 p)

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

@[simp] theorem repr_const (f : FpPoly p) (hf : 0 < FpPoly.degree f) (c : ZMod64 p) :
    repr (const f hf c) = reduceMod f (FpPoly.C c) :=
  rfl

private theorem zmod64_eq_zero_of_modulus_one
    (hp : p = 1) (a : ZMod64 p) : a = 0 := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  have ha : a.val.toNat = 0 := by
    exact Nat.lt_one_iff.mp (by simpa [hp] using a.isLt)
  simpa [ZMod64.toNat_eq_val] using ha

private theorem zmod64_zero_ne_one_of_pos_degree
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    (0 : ZMod64 p) ≠ 1 := by
  intro h01
  have h10 : (1 : ZMod64 p) = 0 := h01.symm
  have hp_dvd : p ∣ 1 := (ZMod64.natCast_eq_zero_iff_dvd (p := p) 1).mp h10
  have hp : p = 1 := Nat.dvd_one.mp hp_dvd
  have hall (a : ZMod64 p) : a = 0 := zmod64_eq_zero_of_modulus_one (p := p) hp a
  have hsize : f.coeffs.size = 0 := by
    by_cases hzero : f.coeffs.size = 0
    · exact hzero
    · rcases f.normalized with hsize | hback
      · exact False.elim (hzero hsize)
      · have hpos : 0 < f.coeffs.size := Nat.pos_of_ne_zero hzero
        have hidx : f.coeffs.size - 1 < f.coeffs.size := Nat.sub_lt hpos (by decide)
        have hback_eq :
            f.coeffs.back? = some (f.coeffs[f.coeffs.size - 1]'hidx) := by
          simp [Array.back?_eq_getElem?]
        have hcoeff : f.coeffs[f.coeffs.size - 1]'hidx = (Zero.zero : ZMod64 p) :=
          hall _
        exact False.elim (hback (by simp [hback_eq, hcoeff]))
  have hdeg : FpPoly.degree f = 0 := by
    simp [FpPoly.degree, DensePoly.degree?, DensePoly.size, hsize]
  simp [hdeg] at hf

theorem zero_ne_one (f : FpPoly p) (hf : 0 < FpPoly.degree f) :
    (0 : PolyQuotient f hf) ≠ 1 := by
  intro h
  have hpoly : (0 : FpPoly p) = 1 := by
    calc
      (0 : FpPoly p) = repr (0 : PolyQuotient f hf) := by
        simp [repr_zero]
      _ = repr (1 : PolyQuotient f hf) := by
        simp [h]
      _ = (1 : FpPoly p) := by
        change repr (one f hf) = 1
        simpa [one] using reduceMod_one f hf
  have hcoeff : (0 : ZMod64 p) = 1 := by
    by_cases h10 : (1 : ZMod64 p) = 0
    · exact h10.symm
    · have hcoeffs := congrArg DensePoly.coeffs hpoly
      have hzero_coeffs : DensePoly.coeffs (0 : FpPoly p) = #[] := by rfl
      have hone_coeffs : DensePoly.coeffs (1 : FpPoly p) = #[(1 : ZMod64 p)] := by
        change DensePoly.coeffs (DensePoly.C (1 : ZMod64 p)) = #[(1 : ZMod64 p)]
        exact DensePoly.coeffs_C_of_ne_zero h10
      rw [hzero_coeffs, hone_coeffs] at hcoeffs
      simp at hcoeffs
  exact zmod64_zero_ne_one_of_pos_degree f hf hcoeff

@[simp] theorem natCast_eq_const
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    natCast f hf n = const f hf (n : ZMod64 p) :=
  rfl

@[simp] theorem repr_natCast
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (n : Nat) :
    repr (natCast f hf n) = reduceMod f (FpPoly.C (n : ZMod64 p)) :=
  rfl

theorem natCast_eq_of_zmod64_natCast_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) {m n : Nat}
    (h : (m : ZMod64 p) = (n : ZMod64 p)) :
    (m : PolyQuotient f hf) = n := by
  change const f hf (m : ZMod64 p) = const f hf (n : ZMod64 p)
  rw [h]

theorem natCast_eq_of_mod_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) {m n : Nat}
    (h : m % p = n % p) :
    (m : PolyQuotient f hf) = n :=
  natCast_eq_of_zmod64_natCast_eq f hf
    ((ZMod64.natCast_eq_natCast_iff (p := p) m n).2 h)

theorem natCast_eq_natCast_iff_reduceMod_const_eq
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (m n : Nat) :
    ((m : PolyQuotient f hf) = n) ↔
      reduceMod f (FpPoly.C (m : ZMod64 p)) =
        reduceMod f (FpPoly.C (n : ZMod64 p)) := by
  constructor
  · intro h
    simpa [repr_natCast] using congrArg repr h
  · intro h
    apply ext
    simpa [repr_natCast] using h

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
    repr (-x) = reduceMod f (-repr x) :=
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
  exact reduceMod_add_reduceMod_congr f a b

theorem reduceMod_mul_reduceMod (f : FpPoly p) (a b : FpPoly p) :
    reduceMod f (a * b) = reduceMod f (reduceMod f a * reduceMod f b) := by
  exact reduceMod_mul_reduceMod_congr f a b

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
