import Init.Grind.Ring.Field
import HexGfqRing.Operations

/-!
Typeclass scaffolding for `HexGfqRing`.

This module upgrades `PolyQuotient p f hf` from an executable quotient
carrier with arithmetic operations to the `Lean.Grind.CommRing` surface
promised by the Phase 1 spec. The operations remain executable; the law
proofs are scaffolded for later phases.
-/

namespace HexGfqRing

open HexPolyFp
open Lean.Grind

variable {p : Nat} [NeZero p]

namespace PolyQuotient

variable {f : FpPoly p} {hf : 0 < f.degree}

/-- Canonical equality can be checked on stored representatives. -/
@[ext] theorem ext {x y : PolyQuotient p f hf} (h : x.repr = y.repr) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The quotient zero is represented by the zero polynomial. -/
def zero : PolyQuotient p f hf :=
  ofPoly (f := f) (hf := hf) 0

/-- The quotient one is represented by the constant polynomial `1`. -/
def one : PolyQuotient p f hf :=
  ofPoly (f := f) (hf := hf) (FpPoly.C 1)

instance : Zero (PolyQuotient p f hf) where
  zero := zero

instance : One (PolyQuotient p f hf) where
  one := one

/-- Natural-number casts use repeated addition of the quotient unit. -/
def natCast : Nat → PolyQuotient p f hf
  | 0 => 0
  | n + 1 => natCast n + 1

instance : NatCast (PolyQuotient p f hf) where
  natCast := natCast

instance (n : Nat) : OfNat (PolyQuotient p f hf) n where
  ofNat := natCast n

/-- Integer casts use quotient negation on top of the natural-number cast. -/
instance : IntCast (PolyQuotient p f hf) where
  intCast z :=
    match z with
    | .ofNat n => natCast n
    | .negSucc n => -natCast (n + 1)

instance : SMul Nat (PolyQuotient p f hf) where
  smul n x := (n : PolyQuotient p f hf) * x

instance : SMul Int (PolyQuotient p f hf) where
  smul z x := (z : PolyQuotient p f hf) * x

/-- The representative of quotient zero is the reduced zero polynomial. -/
theorem repr_zero :
    (0 : PolyQuotient p f hf).repr = reduceMod f 0 := by
  rfl

/-- The representative of quotient one is the reduced constant polynomial `1`. -/
theorem repr_one :
    ((One.one : PolyQuotient p f hf)).repr = reduceMod f (FpPoly.C 1) := by
  rfl

/-- Quotient addition is associative. -/
theorem add_assoc (a b c : PolyQuotient p f hf) :
    a + b + c = a + (b + c) := by
  sorry

/-- Quotient addition is commutative. -/
theorem add_comm (a b : PolyQuotient p f hf) :
    a + b = b + a := by
  sorry

/-- Quotient addition has `0` as a right identity. -/
theorem add_zero (a : PolyQuotient p f hf) :
    a + 0 = a := by
  sorry

/-- Quotient addition has `0` as a left identity. -/
theorem zero_add (a : PolyQuotient p f hf) :
    0 + a = a := by
  sorry

/-- Quotient negation gives an additive inverse. -/
theorem neg_add_cancel (a : PolyQuotient p f hf) :
    -a + a = 0 := by
  sorry

/-- Quotient multiplication is associative. -/
theorem mul_assoc (a b c : PolyQuotient p f hf) :
    a * b * c = a * (b * c) := by
  sorry

/-- Quotient multiplication is commutative. -/
theorem mul_comm (a b : PolyQuotient p f hf) :
    a * b = b * a := by
  sorry

/-- Quotient multiplication has `1` as a right identity. -/
theorem mul_one (a : PolyQuotient p f hf) :
    a * 1 = a := by
  sorry

/-- Quotient multiplication has `1` as a left identity. -/
theorem one_mul (a : PolyQuotient p f hf) :
    1 * a = a := by
  sorry

/-- Quotient multiplication distributes over addition on the left. -/
theorem left_distrib (a b c : PolyQuotient p f hf) :
    a * (b + c) = a * b + a * c := by
  sorry

/-- Quotient multiplication distributes over addition on the right. -/
theorem right_distrib (a b c : PolyQuotient p f hf) :
    (a + b) * c = a * c + b * c := by
  sorry

/-- Zero annihilates quotient multiplication on the left. -/
theorem zero_mul (a : PolyQuotient p f hf) :
    0 * a = 0 := by
  sorry

/-- Zero annihilates quotient multiplication on the right. -/
theorem mul_zero (a : PolyQuotient p f hf) :
    a * 0 = 0 := by
  sorry

/-- Natural powers satisfy the expected zero case. -/
theorem pow_zero (a : PolyQuotient p f hf) :
    a ^ 0 = 1 := by
  sorry

/-- Natural powers satisfy the expected successor recursion. -/
theorem pow_succ (a : PolyQuotient p f hf) (n : Nat) :
    a ^ (n + 1) = a ^ n * a := by
  sorry

/-- Successive natural casts differ by `1` as expected. -/
theorem ofNat_succ (n : Nat) :
    OfNat.ofNat (α := PolyQuotient p f hf) (n + 1) =
      OfNat.ofNat (α := PolyQuotient p f hf) n + 1 := by
  sorry

/-- Subtraction is quotient addition with quotient negation. -/
theorem sub_eq_add_neg (a b : PolyQuotient p f hf) :
    a - b = a + -b := by
  sorry

/-- Integer casts commute with negation. -/
theorem intCast_neg (z : Int) :
    Int.cast (R := PolyQuotient p f hf) (-z) = -Int.cast z := by
  sorry

instance instCommRing : CommRing (PolyQuotient p f hf) where
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

end PolyQuotient

instance {f : FpPoly p} {hf : 0 < f.degree} : Zero (PolyQuotient p f hf) :=
  PolyQuotient.instZero

instance {f : FpPoly p} {hf : 0 < f.degree} : One (PolyQuotient p f hf) :=
  PolyQuotient.instOne

instance {f : FpPoly p} {hf : 0 < f.degree} : NatCast (PolyQuotient p f hf) :=
  PolyQuotient.instNatCast

instance {f : FpPoly p} {hf : 0 < f.degree} (n : Nat) : OfNat (PolyQuotient p f hf) n :=
  PolyQuotient.instOfNat n

instance {f : FpPoly p} {hf : 0 < f.degree} : IntCast (PolyQuotient p f hf) :=
  PolyQuotient.instIntCast

instance {f : FpPoly p} {hf : 0 < f.degree} : SMul Nat (PolyQuotient p f hf) :=
  PolyQuotient.instSMulNat

instance {f : FpPoly p} {hf : 0 < f.degree} : SMul Int (PolyQuotient p f hf) :=
  PolyQuotient.instSMulInt

instance {f : FpPoly p} {hf : 0 < f.degree} : CommRing (PolyQuotient p f hf) :=
  PolyQuotient.instCommRing

end HexGfqRing
