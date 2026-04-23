import HexGfqRing.Core

/-!
Executable quotient-ring operations for `HexGfqRing`.

This module upgrades `PolyQuotient p f hf` from a canonical-representative
carrier to the next Phase 1 API slice promised by the spec: executable
addition, negation, subtraction, multiplication, and exponentiation, each
normalizing through `reduceMod`, together with the first `repr` formulas for
those operations.
-/

namespace HexGfqRing

open HexPolyFp

variable {p : Nat} [NeZero p]

/-- Coefficientwise negation on `FpPoly`, followed by canonical normalization. -/
private def polyNeg (a : FpPoly p) : FpPoly p :=
  HexPoly.DensePoly.ofArray (a.coeffs.map Neg.neg)

/-- The constant polynomial `1` in `FpPoly`. -/
private def polyOne : FpPoly p :=
  FpPoly.C 1

/-- Simple recursive polynomial exponentiation for the quotient scaffold. -/
private def polyPow (a : FpPoly p) : Nat → FpPoly p
  | 0 => polyOne
  | n + 1 => FpPoly.mul (polyPow a n) a

namespace PolyQuotient

variable {f : FpPoly p} {hf : 0 < f.degree}

/-- Quotient elements are determined by their canonical representatives. -/
@[ext] theorem ext {x y : PolyQuotient p f hf} (h : x.repr = y.repr) : x = y := by
  cases x
  cases y
  cases h
  simp

/-- `0` is represented by the zero polynomial reduced modulo `f`. -/
instance : Zero (PolyQuotient p f hf) where
  zero := ofPoly (f := f) (hf := hf) 0

/-- `1` is represented by the constant polynomial `1` reduced modulo `f`. -/
instance : One (PolyQuotient p f hf) where
  one := ofPoly (f := f) (hf := hf) polyOne

/-- Quotient addition is canonical polynomial addition followed by reduction. -/
instance : Add (PolyQuotient p f hf) where
  add x y := ofPoly (f := f) (hf := hf) (FpPoly.add x.repr y.repr)

/-- Quotient negation is canonical polynomial negation followed by reduction. -/
instance : Neg (PolyQuotient p f hf) where
  neg x := ofPoly (f := f) (hf := hf) (polyNeg x.repr)

/-- Quotient subtraction is canonical polynomial subtraction followed by reduction. -/
instance : Sub (PolyQuotient p f hf) where
  sub x y := ofPoly (f := f) (hf := hf) (FpPoly.sub x.repr y.repr)

/-- Quotient multiplication is canonical polynomial multiplication followed by reduction. -/
instance : Mul (PolyQuotient p f hf) where
  mul x y := ofPoly (f := f) (hf := hf) (FpPoly.mul x.repr y.repr)

/--
Natural powers are computed by repeated quotient multiplication so every step
passes back through `reduceMod`.
-/
instance instPowNat : Pow (PolyQuotient p f hf) Nat where
  pow x n := ofPoly (f := f) (hf := hf) (polyPow x.repr n)

/-- The quotient zero stores the reduced zero polynomial. -/
theorem zero_repr :
    (0 : PolyQuotient p f hf).repr = reduceMod f 0 := by
  rfl

/-- The quotient one stores the reduced constant polynomial. -/
theorem one_repr :
    (1 : PolyQuotient p f hf).repr = reduceMod f polyOne := by
  rfl

/-- Quotient addition reduces the sum of canonical representatives. -/
theorem add_repr (x y : PolyQuotient p f hf) :
    (x + y).repr = reduceMod f (FpPoly.add x.repr y.repr) := by
  rfl

/-- Quotient negation reduces the negated canonical representative. -/
theorem neg_repr (x : PolyQuotient p f hf) :
    (-x).repr = reduceMod f (polyNeg x.repr) := by
  rfl

/-- Quotient subtraction reduces the difference of canonical representatives. -/
theorem sub_repr (x y : PolyQuotient p f hf) :
    (x - y).repr = reduceMod f (FpPoly.sub x.repr y.repr) := by
  rfl

/-- Quotient multiplication reduces the product of canonical representatives. -/
theorem mul_repr (x y : PolyQuotient p f hf) :
    (x * y).repr = reduceMod f (FpPoly.mul x.repr y.repr) := by
  rfl

/-- Quotient powers reduce the corresponding polynomial power representative. -/
theorem pow_repr (x : PolyQuotient p f hf) (n : Nat) :
    (x ^ n).repr = reduceMod f (polyPow x.repr n) := by
  rfl

end PolyQuotient

/-- Top-level projection reads the reduced zero representative. -/
theorem repr_zero {f : FpPoly p} {hf : 0 < f.degree} :
    repr (0 : PolyQuotient p f hf) = reduceMod f 0 := by
  rfl

/-- Top-level projection reads the reduced unit representative. -/
theorem repr_one {f : FpPoly p} {hf : 0 < f.degree} :
    repr (1 : PolyQuotient p f hf) = reduceMod f polyOne := by
  rfl

/-- Top-level `repr` turns quotient addition into reduced polynomial addition. -/
theorem repr_add {f : FpPoly p} {hf : 0 < f.degree} (x y : PolyQuotient p f hf) :
    repr (x + y) = reduceMod f (FpPoly.add (repr x) (repr y)) := by
  rfl

/-- Top-level `repr` turns quotient negation into reduced polynomial negation. -/
theorem repr_neg {f : FpPoly p} {hf : 0 < f.degree} (x : PolyQuotient p f hf) :
    repr (-x) = reduceMod f (polyNeg (repr x)) := by
  rfl

/-- Top-level `repr` turns quotient subtraction into reduced polynomial subtraction. -/
theorem repr_sub {f : FpPoly p} {hf : 0 < f.degree} (x y : PolyQuotient p f hf) :
    repr (x - y) = reduceMod f (FpPoly.sub (repr x) (repr y)) := by
  rfl

/-- Top-level `repr` turns quotient multiplication into reduced polynomial multiplication. -/
theorem repr_mul {f : FpPoly p} {hf : 0 < f.degree} (x y : PolyQuotient p f hf) :
    repr (x * y) = reduceMod f (FpPoly.mul (repr x) (repr y)) := by
  rfl

/-- Top-level `repr` turns quotient powers into reduced polynomial powers. -/
theorem repr_pow {f : FpPoly p} {hf : 0 < f.degree} (x : PolyQuotient p f hf) (n : Nat) :
    repr (x ^ n) = reduceMod f (polyPow (repr x) n) := by
  simpa using PolyQuotient.pow_repr (f := f) (hf := hf) x n

end HexGfqRing
