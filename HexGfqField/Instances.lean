import Init.Grind.Ring.Field
import HexGfqField.Ops

/-!
Typeclass scaffolding for `HexGfqField`.

This module upgrades the thin `FiniteField p f hf hirr` wrapper from the
carrier-plus-operations scaffold to the spec-facing `Lean.Grind.Field`
surface. The executable data remains delegated to the shared quotient
representation from `HexGfqRing`; Phase 1 only packages that data under
the expected additive, casting, characteristic, and field-law interfaces.
-/

namespace HexGfqField

open HexPolyFp
open Lean.Grind

variable {p : Nat} [NeZero p]

namespace FiniteField

variable {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}

/-- Finite-field addition reuses quotient-ring addition. -/
def add (x y : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  ofQuotient (hirr := hirr) (x.toQuotient + y.toQuotient)

/-- Finite-field negation reuses quotient-ring negation. -/
def neg (x : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  ofQuotient (hirr := hirr) (-x.toQuotient)

/-- Finite-field subtraction reuses quotient-ring subtraction. -/
def sub (x y : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  ofQuotient (hirr := hirr) (x.toQuotient - y.toQuotient)

instance : Add (FiniteField p f hf hirr) where
  add := add

instance : Neg (FiniteField p f hf hirr) where
  neg := neg

instance : Sub (FiniteField p f hf hirr) where
  sub := sub

instance : NatCast (FiniteField p f hf hirr) where
  natCast n := ofQuotient (hirr := hirr) n

instance (n : Nat) : OfNat (FiniteField p f hf hirr) n where
  ofNat := ofQuotient (hirr := hirr) n

instance : IntCast (FiniteField p f hf hirr) where
  intCast z := ofQuotient (hirr := hirr) z

instance : SMul Nat (FiniteField p f hf hirr) where
  smul n x := ofQuotient (hirr := hirr) (n • x.toQuotient)

instance : SMul Int (FiniteField p f hf hirr) where
  smul z x := ofQuotient (hirr := hirr) (z • x.toQuotient)

/-- Integer exponentiation uses inversion on negative powers. -/
def zpow (x : FiniteField p f hf hirr) : Int → FiniteField p f hf hirr
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

instance : HPow (FiniteField p f hf hirr) Int (FiniteField p f hf hirr) where
  hPow := zpow

/-- Addition is associative on the wrapped quotient carrier. -/
theorem add_assoc (a b c : FiniteField p f hf hirr) :
    a + b + c = a + (b + c) := by
  sorry

/-- Addition is commutative on the wrapped quotient carrier. -/
theorem add_comm (a b : FiniteField p f hf hirr) :
    a + b = b + a := by
  sorry

/-- Zero is a right identity for finite-field addition. -/
theorem add_zero (a : FiniteField p f hf hirr) :
    a + 0 = a := by
  sorry

/-- Negation gives an additive inverse on the wrapped quotient carrier. -/
theorem neg_add_cancel (a : FiniteField p f hf hirr) :
    -a + a = 0 := by
  sorry

/-- Multiplication is associative on the wrapped quotient carrier. -/
theorem mul_assoc (a b c : FiniteField p f hf hirr) :
    a * b * c = a * (b * c) := by
  sorry

/-- Multiplication is commutative on the wrapped quotient carrier. -/
theorem mul_comm (a b : FiniteField p f hf hirr) :
    a * b = b * a := by
  sorry

/-- One is a right identity for finite-field multiplication. -/
theorem mul_one (a : FiniteField p f hf hirr) :
    a * 1 = a := by
  sorry

/-- One is a left identity for finite-field multiplication. -/
theorem one_mul (a : FiniteField p f hf hirr) :
    1 * a = a := by
  sorry

/-- Multiplication distributes over addition on the left. -/
theorem left_distrib (a b c : FiniteField p f hf hirr) :
    a * (b + c) = a * b + a * c := by
  sorry

/-- Multiplication distributes over addition on the right. -/
theorem right_distrib (a b c : FiniteField p f hf hirr) :
    (a + b) * c = a * c + b * c := by
  sorry

/-- Zero annihilates multiplication on the left. -/
theorem zero_mul (a : FiniteField p f hf hirr) :
    0 * a = 0 := by
  sorry

/-- Zero annihilates multiplication on the right. -/
theorem mul_zero (a : FiniteField p f hf hirr) :
    a * 0 = 0 := by
  sorry

/-- Natural powers satisfy the expected zero case. -/
theorem pow_zero (a : FiniteField p f hf hirr) :
    a ^ 0 = 1 := by
  sorry

/-- Natural powers satisfy the expected successor recursion. -/
theorem pow_succ (a : FiniteField p f hf hirr) (n : Nat) :
    a ^ (n + 1) = a ^ n * a := by
  sorry

/-- Successive natural-number casts differ by `1` as expected. -/
theorem ofNat_succ (n : Nat) :
    OfNat.ofNat (α := FiniteField p f hf hirr) (n + 1) =
      OfNat.ofNat (α := FiniteField p f hf hirr) n + 1 := by
  sorry

/-- Subtraction is definitionally addition with negation. -/
theorem sub_eq_add_neg (a b : FiniteField p f hf hirr) :
    a - b = a + -b := by
  sorry

/-- Integer casts commute with negation on the wrapped quotient carrier. -/
theorem intCast_neg (z : Int) :
    Int.cast (R := FiniteField p f hf hirr) (-z) = -Int.cast z := by
  sorry

/-- Irreducible quotient-field wrappers are nontrivial. -/
theorem zero_ne_one :
    (0 : FiniteField p f hf hirr) ≠ 1 := by
  sorry

/-- The executable inverse uses the standard zero junk-value convention. -/
theorem inv_zero :
    (0 : FiniteField p f hf hirr)⁻¹ = 0 := by
  sorry

/-- Integer powers satisfy the expected zero case. -/
theorem zpow_zero (a : FiniteField p f hf hirr) :
    a ^ (0 : Int) = 1 := by
  sorry

/-- Integer powers satisfy the expected positive successor recursion. -/
theorem zpow_succ (a : FiniteField p f hf hirr) (n : Nat) :
    a ^ (n + 1 : Int) = a ^ (n : Int) * a := by
  sorry

/-- Negative powers use inversion of the corresponding positive power. -/
theorem zpow_neg (a : FiniteField p f hf hirr) (n : Int) :
    a ^ (-n) = (a ^ n)⁻¹ := by
  sorry

instance instField : Field (FiniteField p f hf hirr) where
  nsmul := inferInstance
  zsmul := inferInstance
  natCast := inferInstance
  intCast := inferInstance
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  nsmul_eq_natCast_mul n a := by
    sorry
  pow_zero := pow_zero
  pow_succ := pow_succ
  ofNat_succ := ofNat_succ
  sub_eq_add_neg := sub_eq_add_neg
  intCast_ofNat n := by
    sorry
  intCast_neg := intCast_neg
  neg_zsmul i a := by
    sorry
  zsmul_natCast_eq_nsmul n a := by
    sorry
  div_eq_mul_inv := by
    intro a b
    exact HexGfqField.FiniteField.div_eq_mul_inv a b
  zero_ne_one := zero_ne_one
  inv_zero := inv_zero
  mul_inv_cancel := by
    intro a ha
    exact HexGfqField.FiniteField.mul_inv_cancel a ha
  zpow := inferInstance
  zpow_zero := zpow_zero
  zpow_succ := zpow_succ
  zpow_neg := zpow_neg

/-- Natural-number casts vanish exactly on multiples of the characteristic. -/
theorem ofNat_eq_zero_iff (x : Nat) :
    OfNat.ofNat (α := FiniteField p f hf hirr) x = 0 ↔ x % p = 0 := by
  sorry

instance instIsCharP : IsCharP (FiniteField p f hf hirr) p :=
  IsCharP.mk' p (FiniteField p f hf hirr) <| by
    intro x
    simpa using (ofNat_eq_zero_iff (p := p) (f := f) (hf := hf) (hirr := hirr) x)

end FiniteField

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    Add (FiniteField p f hf hirr) :=
  FiniteField.instAdd

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    Neg (FiniteField p f hf hirr) :=
  FiniteField.instNeg

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    Sub (FiniteField p f hf hirr) :=
  FiniteField.instSub

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    NatCast (FiniteField p f hf hirr) :=
  FiniteField.instNatCast

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} (n : Nat) :
    OfNat (FiniteField p f hf hirr) n :=
  FiniteField.instOfNat n

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    IntCast (FiniteField p f hf hirr) :=
  FiniteField.instIntCast

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    SMul Nat (FiniteField p f hf hirr) :=
  FiniteField.instSMulNat

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    SMul Int (FiniteField p f hf hirr) :=
  FiniteField.instSMulInt

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    Field (FiniteField p f hf hirr) :=
  FiniteField.instField

instance {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f} :
    IsCharP (FiniteField p f hf hirr) p :=
  FiniteField.instIsCharP

end HexGfqField
