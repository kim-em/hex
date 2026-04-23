import HexGfqRing.Core

/-!
Executable quotient-ring operations for `HexGfqRing`.

This module adds the canonical arithmetic surface on
`PolyQuotient p f hf`: addition, negation, subtraction, multiplication,
and exponentiation. Each operation normalizes through `reduceMod`, and
the accompanying `repr_*` lemmas expose the stored representative
formula needed by downstream quotient-ring and finite-field code.
-/

namespace HexGfqRing

open HexPolyFp

variable {p : Nat} [NeZero p]

namespace PolyQuotient

variable {f : FpPoly p} {hf : 0 < f.degree}

/-- Quotient addition reduces the sum of representatives modulo `f`. -/
def add (x y : PolyQuotient p f hf) : PolyQuotient p f hf :=
  ofPoly (f := f) (hf := hf) (x.repr + y.repr)

/-- Quotient negation reduces the additive inverse of the representative modulo `f`. -/
def neg (x : PolyQuotient p f hf) : PolyQuotient p f hf :=
  ofPoly (f := f) (hf := hf) (0 - x.repr)

/-- Quotient subtraction reduces the difference of representatives modulo `f`. -/
def sub (x y : PolyQuotient p f hf) : PolyQuotient p f hf :=
  ofPoly (f := f) (hf := hf) (x.repr - y.repr)

/-- Quotient multiplication reduces the product of representatives modulo `f`. -/
def mul (x y : PolyQuotient p f hf) : PolyQuotient p f hf :=
  ofPoly (f := f) (hf := hf) (x.repr * y.repr)

/--
Quotient exponentiation uses the existing modular-power scaffold on the
canonical representative and normalizes the result through `reduceMod`.
-/
def pow (x : PolyQuotient p f hf) (n : Nat) : PolyQuotient p f hf :=
  ofPoly (f := f) (hf := hf) (FpPoly.powModMonic x.repr n f)

instance : Add (PolyQuotient p f hf) where
  add := add

instance : Neg (PolyQuotient p f hf) where
  neg := neg

instance : Sub (PolyQuotient p f hf) where
  sub := sub

instance : Mul (PolyQuotient p f hf) where
  mul := mul

instance : Pow (PolyQuotient p f hf) Nat where
  pow := pow

/-- The representative of a sum is the reduced sum of representatives. -/
theorem repr_add (x y : PolyQuotient p f hf) :
    (x + y).repr = reduceMod f (x.repr + y.repr) := by
  rfl

/-- The representative of a negation is the reduced additive inverse. -/
theorem repr_neg (x : PolyQuotient p f hf) :
    (-x).repr = reduceMod f (0 - x.repr) := by
  rfl

/-- The representative of a difference is the reduced difference of representatives. -/
theorem repr_sub (x y : PolyQuotient p f hf) :
    (x - y).repr = reduceMod f (x.repr - y.repr) := by
  rfl

/-- The representative of a product is the reduced product of representatives. -/
theorem repr_mul (x y : PolyQuotient p f hf) :
    (x * y).repr = reduceMod f (x.repr * y.repr) := by
  rfl

/--
The representative of a power is the reduced modular-power scaffold on
the canonical representative.
-/
theorem repr_pow (x : PolyQuotient p f hf) (n : Nat) :
    (x ^ n).repr = reduceMod f (FpPoly.powModMonic x.repr n f) := by
  rfl

end PolyQuotient

/-- Top-level `repr` formula for quotient addition. -/
theorem repr_add {f : FpPoly p} {hf : 0 < f.degree} (x y : PolyQuotient p f hf) :
    repr (x + y) = reduceMod f (repr x + repr y) := by
  rfl

/-- Top-level `repr` formula for quotient negation. -/
theorem repr_neg {f : FpPoly p} {hf : 0 < f.degree} (x : PolyQuotient p f hf) :
    repr (-x) = reduceMod f (0 - repr x) := by
  rfl

/-- Top-level `repr` formula for quotient subtraction. -/
theorem repr_sub {f : FpPoly p} {hf : 0 < f.degree} (x y : PolyQuotient p f hf) :
    repr (x - y) = reduceMod f (repr x - repr y) := by
  rfl

/-- Top-level `repr` formula for quotient multiplication. -/
theorem repr_mul {f : FpPoly p} {hf : 0 < f.degree} (x y : PolyQuotient p f hf) :
    repr (x * y) = reduceMod f (repr x * repr y) := by
  rfl

/-- Top-level `repr` formula for quotient exponentiation. -/
theorem repr_pow {f : FpPoly p} {hf : 0 < f.degree} (x : PolyQuotient p f hf) (n : Nat) :
    repr (x ^ n) = reduceMod f (FpPoly.powModMonic (repr x) n f) := by
  rfl

end HexGfqRing
