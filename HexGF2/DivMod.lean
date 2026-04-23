import HexGF2.Mul

/-!
Packed polynomial division scaffolding for `GF(2)`.

This module adds executable division with remainder for `GF2Poly` using the
existing XOR and shift operations. The algebraic correctness proofs remain
Phase 1 scaffolding obligations.
-/

namespace HexGF2

namespace GF2Poly

/-- Quotient and remainder returned by packed `GF(2)` polynomial division. -/
structure DivMod where
  quotient : GF2Poly
  remainder : GF2Poly

/-- The packed monomial `X^n`. -/
def monomial (n : Nat) : GF2Poly :=
  let words0 : Array UInt64 := (List.replicate (n / 64 + 1) (0 : UInt64)).toArray
  let wordIdx := n / 64
  let bit := (1 : UInt64) <<< (UInt64.ofNat (n % 64))
  ofWords (words0.set! wordIdx bit)

/--
Fuel-bounded division loop for packed `GF(2)` polynomials.

Each step cancels the leading term of the remainder by XORing a shifted copy
of the divisor, matching subtraction over `GF(2)`.
-/
private def divModAux : Nat → GF2Poly → GF2Poly → GF2Poly → DivMod
  | 0, quotient, remainder, _ =>
      { quotient := quotient, remainder := remainder }
  | fuel + 1, quotient, remainder, divisor =>
      if divisor.words.isEmpty || remainder.words.isEmpty then
        { quotient := quotient, remainder := remainder }
      else if divisor.degree ≤ remainder.degree then
        let shift := remainder.degree - divisor.degree
        let term := monomial shift
        let remainder' := remainder + shiftLeft divisor shift
        divModAux fuel (quotient + term) remainder' divisor
      else
        { quotient := quotient, remainder := remainder }

/--
Divide packed `GF(2)` polynomials, returning quotient and remainder.

Division by the zero polynomial returns zero quotient and the original
dividend as remainder.
-/
def divMod (dividend divisor : GF2Poly) : DivMod :=
  if divisor.words.isEmpty then
    { quotient := ofWords #[], remainder := dividend }
  else
    divModAux (dividend.degree + 1) (ofWords #[]) dividend divisor

/-- Quotient from packed `GF(2)` polynomial division. -/
def div (dividend divisor : GF2Poly) : GF2Poly :=
  (divMod dividend divisor).quotient

/-- Remainder from packed `GF(2)` polynomial division. -/
def mod (dividend divisor : GF2Poly) : GF2Poly :=
  (divMod dividend divisor).remainder

instance : Div GF2Poly where
  div := div

instance : Mod GF2Poly where
  mod := mod

/-- Packed `GF(2)` quotient projection is definitionally `divMod`'s first field. -/
theorem div_eq_quotient (dividend divisor : GF2Poly) :
    dividend / divisor = (divMod dividend divisor).quotient := by
  rfl

/-- Packed `GF(2)` remainder projection is definitionally `divMod`'s second field. -/
theorem mod_eq_remainder (dividend divisor : GF2Poly) :
    dividend % divisor = (divMod dividend divisor).remainder := by
  rfl

/-- The division algorithm reconstructs the dividend from quotient and remainder. -/
theorem div_mul_add_mod (dividend divisor : GF2Poly)
    (hdivisor : ¬ divisor.IsZero) :
    divisor * (dividend / divisor) + (dividend % divisor) = dividend := by
  sorry

/-- A nonzero packed remainder has degree strictly smaller than the divisor. -/
theorem mod_degree_lt (dividend divisor : GF2Poly)
    (hdivisor : ¬ divisor.IsZero)
    (hrem : ¬ (dividend % divisor).IsZero) :
    (dividend % divisor).degree < divisor.degree := by
  sorry

end GF2Poly

end HexGF2
