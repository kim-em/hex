import HexGf2.Mul

/-!
Packed division-with-remainder scaffolding for `GF(2)` polynomials.

This module adds the Phase 1 quotient/remainder API for `GF2Poly`,
implementing executable long division on packed words together with the
immediate theorem surface used by later gcd and modular-reduction layers.
-/

namespace HexGf2

namespace GF2Poly

/-- Quotient and remainder returned by packed `GF(2)` polynomial division. -/
structure DivMod where
  quotient : GF2Poly
  remainder : GF2Poly

/-- The packed zero polynomial. -/
def zero : GF2Poly :=
  ofWords #[]

/-- The monomial `X^n` in packed `GF(2)` form. -/
def monomial (n : Nat) : GF2Poly :=
  let wordCount := n / 64 + 1
  let words0 : Array UInt64 := (List.replicate wordCount (0 : UInt64)).toArray
  let wordIdx := n / 64
  let bit := (1 : UInt64) <<< (UInt64.ofNat (n % 64))
  ofWords (words0.set! wordIdx bit)

/--
Fuel-bounded long division for packed `GF(2)` polynomials.

Each step cancels the leading term of the current remainder by XORing in a
shifted copy of the divisor, matching subtraction over `GF(2)`.
-/
private def divModAux : Nat → GF2Poly → GF2Poly → GF2Poly → DivMod
  | 0, quotient, remainder, _ =>
      { quotient := quotient, remainder := remainder }
  | fuel + 1, quotient, remainder, divisor =>
      if remainder.words.isEmpty then
        { quotient := quotient, remainder := remainder }
      else if divisor.degree ≤ remainder.degree then
        let shift := remainder.degree - divisor.degree
        let term := monomial shift
        divModAux fuel (quotient + term) (remainder + term * divisor) divisor
      else
        { quotient := quotient, remainder := remainder }

/--
Packed polynomial division with remainder over `GF(2)`.

Division by the zero polynomial leaves the dividend untouched in the
remainder slot.
-/
def divMod (dividend divisor : GF2Poly) : DivMod :=
  if divisor.words.isEmpty then
    { quotient := zero, remainder := dividend }
  else
    divModAux (dividend.degree + 1) zero dividend divisor

/-- Quotient from packed `GF(2)` division. -/
def div (dividend divisor : GF2Poly) : GF2Poly :=
  (divMod dividend divisor).quotient

/-- Remainder from packed `GF(2)` division. -/
def mod (dividend divisor : GF2Poly) : GF2Poly :=
  (divMod dividend divisor).remainder

instance : Div GF2Poly where
  div := div

instance : Mod GF2Poly where
  mod := mod

/-- The packed zero polynomial is definitionally `ofWords #[]`. -/
theorem zero_eq_ofWords_nil : zero = ofWords #[] := by
  rfl

/-- `monomial` builds `X^n` by normalizing a single set bit. -/
theorem monomial_eq_ofWords_singleton (n : Nat) :
    monomial n =
      ofWords (((List.replicate (n / 64 + 1) (0 : UInt64)).toArray).set!
        (n / 64) ((1 : UInt64) <<< (UInt64.ofNat (n % 64)))) := by
  rfl

/-- Packed division is definitionally the quotient field of `divMod`. -/
theorem div_eq_quotient (dividend divisor : GF2Poly) :
    dividend / divisor = (divMod dividend divisor).quotient := by
  rfl

/-- Packed remainder is definitionally the remainder field of `divMod`. -/
theorem mod_eq_remainder (dividend divisor : GF2Poly) :
    dividend % divisor = (divMod dividend divisor).remainder := by
  rfl

/-- Division by the packed zero polynomial returns zero quotient. -/
theorem divMod_zero_right (dividend : GF2Poly) :
    divMod dividend zero = { quotient := zero, remainder := dividend } := by
  sorry

/-- Packed division satisfies the Euclidean identity over nonzero divisors. -/
theorem div_mul_add_mod (dividend divisor : GF2Poly)
    (hdivisor : ¬ divisor.IsZero) :
    divisor * (dividend / divisor) + (dividend % divisor) = dividend := by
  sorry

/-- The nonzero packed remainder has degree smaller than the divisor. -/
theorem mod_degree_lt (dividend divisor : GF2Poly)
    (hdivisor : ¬ divisor.IsZero) :
    (dividend % divisor).IsZero ∨ (dividend % divisor).degree < divisor.degree := by
  sorry

end GF2Poly

end HexGf2
