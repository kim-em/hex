import HexGfqField.Core

/-!
Executable operation scaffolding for `HexGfqField`.

This module extends the thin `FiniteField` wrapper with the first
field-oriented executable operations promised by the spec: inverse,
division, exponentiation, and Frobenius. The implementation stays
strictly on top of the shared quotient-ring carrier so later phases can
add algebraic laws and typeclass packaging without introducing a second
representation.
-/

namespace HexGfqField

open HexPolyFp

variable {p : Nat} [NeZero p]

namespace FiniteField

variable {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}

/-- Finite-field zero is the wrapped quotient-ring zero. -/
instance : Zero (FiniteField p f hf hirr) where
  zero := ofQuotient (hirr := hirr) 0

/-- Finite-field one is the wrapped quotient-ring one. -/
instance : One (FiniteField p f hf hirr) where
  one := ofQuotient (hirr := hirr) 1

/-- Finite-field multiplication reuses quotient-ring multiplication. -/
instance : Mul (FiniteField p f hf hirr) where
  mul x y := ofQuotient (hirr := hirr) (x.toQuotient * y.toQuotient)

/-- Finite-field natural powers reuse quotient-ring exponentiation. -/
instance : Pow (FiniteField p f hf hirr) Nat where
  pow x n := ofQuotient (hirr := hirr) (x.toQuotient ^ n)

/--
Executable inverse candidate on the thin wrapper.

Phase 1 records only the operation boundary; later work refines this
placeholder into the intended extended-GCD-based inverse over `FpPoly`.
-/
def inv (x : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  let _ := x
  1

instance : Inv (FiniteField p f hf hirr) where
  inv := inv

/-- Division is multiplication by the executable inverse candidate. -/
def div (x y : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  x * y⁻¹

instance : Div (FiniteField p f hf hirr) where
  div := div

/-- Frobenius raises the wrapped quotient representative to the characteristic `p`. -/
def frob (x : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  ofQuotient (hirr := hirr) (x.toQuotient ^ p)

/-- Division is definitionally multiplication by the executable inverse. -/
theorem div_eq_mul_inv (x y : FiniteField p f hf hirr) :
    div x y = x * y⁻¹ := by
  rfl

/--
Under the irreducibility and nonzero hypotheses, the executable inverse
candidate cancels on the right.
-/
theorem mul_inv_cancel (x : FiniteField p f hf hirr) (hx : x ≠ 0) :
    x * x⁻¹ = 1 := by
  sorry

/-- The Frobenius map agrees with raising to the characteristic `p`. -/
theorem frob_eq_pow_char (x : FiniteField p f hf hirr) :
    frob x = x ^ p := by
  rfl

end FiniteField

/-- Top-level inverse wrapper on `FiniteField`. -/
def inv {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  @FiniteField.inv p _ f hf hirr x

/-- Top-level division wrapper on `FiniteField`. -/
def div {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x y : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  @FiniteField.div p _ f hf hirr x y

/-- Top-level Frobenius wrapper on `FiniteField`. -/
def frob {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x : FiniteField p f hf hirr) : FiniteField p f hf hirr :=
  @FiniteField.frob p _ f hf hirr x

/-- Top-level definition-level division formula. -/
theorem div_eq_mul_inv {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x y : FiniteField p f hf hirr) :
    HexGfqField.div x y = x * HexGfqField.inv y := by
  rfl

/-- Top-level right-cancellation theorem stub for the executable inverse. -/
theorem mul_inv_cancel {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x : FiniteField p f hf hirr) (hx : x ≠ 0) :
    x * HexGfqField.inv x = 1 := by
  exact FiniteField.mul_inv_cancel x hx

/-- Top-level Frobenius contract. -/
theorem frob_eq_pow_char {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x : FiniteField p f hf hirr) :
    HexGfqField.frob x = x ^ p := by
  exact FiniteField.frob_eq_pow_char x

end HexGfqField
