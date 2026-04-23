import HexPolyFp.Core

/-!
Modular-power and Frobenius scaffolding for `FpPoly`.

This module records the first theorem surface around the executable
`powModMonic`, `frobeniusModMonic`, and `frobeniusPowModMonic`
entry points from `HexPolyFp.Core`. The declarations state the
intended normalization, reduced-remainder, repeated-squaring, and
iterated-Frobenius contracts needed by downstream quotient-ring and
factorization libraries.
-/

namespace HexPolyFp

namespace FpPoly

open HexModArith

variable {p : Nat} [NeZero p]

/--
Naive modular-power recursion used to specify the intended repeated
multiplication semantics of `powModMonic`.
-/
def naivePowModMonic (base modulus : FpPoly p) : Nat → FpPoly p
  | 0 => C 1
  | n + 1 => modMonic (mul (naivePowModMonic base modulus n) (modMonic base modulus)) modulus

/--
Explicit Frobenius iteration helper used to state the intended semantics
of `frobeniusPowModMonic`.
-/
def iterateFrobeniusModMonic (modulus : FpPoly p) : Nat → FpPoly p → FpPoly p
  | 0, f => modMonic f modulus
  | k + 1, f => frobeniusModMonic (iterateFrobeniusModMonic modulus k f) modulus

/-- Modular powers are returned in normalized dense-polynomial form. -/
theorem powModMonic_isNormalized (base modulus : FpPoly p) (n : Nat) :
    HexPoly.DensePoly.IsNormalized (powModMonic base n modulus).coeffs := by
  simpa [HexPoly.DensePoly.IsNormalized] using (powModMonic base n modulus).normalized

/--
Reducing a modular power again modulo the same monic polynomial does not
change the result.
-/
theorem powModMonic_modMonic_self (base modulus : FpPoly p) (n : Nat) :
    modMonic (powModMonic base n modulus) modulus = powModMonic base n modulus := by
  sorry

/--
For nonzero monic moduli, a modular power is either zero or has degree
strictly below the modulus.
-/
theorem powModMonic_degree_lt (base modulus : FpPoly p) (n : Nat)
    (hmonic : HexPoly.DensePoly.Monic modulus) (hmodulus : modulus ≠ 0) :
    (powModMonic base n modulus).natDegree? = none ∨
      (powModMonic base n modulus).degree < modulus.degree := by
  sorry

/--
The repeated-squaring executable shell agrees with the naive repeated
multiplication recursion modulo the same monic polynomial.
-/
theorem powModMonic_eq_naivePowModMonic (base modulus : FpPoly p) (n : Nat) :
    powModMonic base n modulus = naivePowModMonic base modulus n := by
  sorry

/-- The Frobenius entry point is definitionally the `p`-th modular power. -/
theorem frobeniusModMonic_eq_powModMonic (f modulus : FpPoly p) :
    frobeniusModMonic f modulus = powModMonic f p modulus := by
  rfl

/-- Frobenius outputs are normalized dense polynomials. -/
theorem frobeniusModMonic_isNormalized (f modulus : FpPoly p) :
    HexPoly.DensePoly.IsNormalized (frobeniusModMonic f modulus).coeffs := by
  simpa [frobeniusModMonic_eq_powModMonic] using
    powModMonic_isNormalized (base := f) (modulus := modulus) (n := p)

/-- Reducing the Frobenius output again does not change it. -/
theorem frobeniusModMonic_modMonic_self (f modulus : FpPoly p) :
    modMonic (frobeniusModMonic f modulus) modulus = frobeniusModMonic f modulus := by
  simpa [frobeniusModMonic_eq_powModMonic] using
    powModMonic_modMonic_self (base := f) (modulus := modulus) (n := p)

/-- The Frobenius output stays in reduced remainder form. -/
theorem frobeniusModMonic_degree_lt (f modulus : FpPoly p)
    (hmonic : HexPoly.DensePoly.Monic modulus) (hmodulus : modulus ≠ 0) :
    (frobeniusModMonic f modulus).natDegree? = none ∨
      (frobeniusModMonic f modulus).degree < modulus.degree := by
  simpa [frobeniusModMonic_eq_powModMonic] using
    powModMonic_degree_lt (base := f) (modulus := modulus) (n := p) hmonic hmodulus

/--
The iterated Frobenius entry point is definitionally the modular power
with exponent `p ^ k`.
-/
theorem frobeniusPowModMonic_eq_powModMonic (f modulus : FpPoly p) (k : Nat) :
    frobeniusPowModMonic f modulus k = powModMonic f (p ^ k) modulus := by
  rfl

/-- Zero Frobenius iterations return the original reduced polynomial. -/
theorem frobeniusPowModMonic_zero (f modulus : FpPoly p) :
    frobeniusPowModMonic f modulus 0 = modMonic f modulus := by
  sorry

/--
Successive Frobenius iterations agree with repeatedly applying the
single-step Frobenius map modulo the same polynomial.
-/
theorem frobeniusPowModMonic_succ (f modulus : FpPoly p) (k : Nat) :
    frobeniusPowModMonic f modulus (k + 1) =
      frobeniusModMonic (frobeniusPowModMonic f modulus k) modulus := by
  sorry

/-- Iterated Frobenius agrees with repeated single-step Frobenius action. -/
theorem frobeniusPowModMonic_eq_iterate (f modulus : FpPoly p) (k : Nat) :
    frobeniusPowModMonic f modulus k =
      iterateFrobeniusModMonic modulus k f := by
  sorry

/-- Iterated Frobenius outputs are normalized dense polynomials. -/
theorem frobeniusPowModMonic_isNormalized (f modulus : FpPoly p) (k : Nat) :
    HexPoly.DensePoly.IsNormalized (frobeniusPowModMonic f modulus k).coeffs := by
  simpa [frobeniusPowModMonic_eq_powModMonic] using
    powModMonic_isNormalized (base := f) (modulus := modulus) (n := p ^ k)

/-- Reducing an iterated Frobenius output again does not change it. -/
theorem frobeniusPowModMonic_modMonic_self (f modulus : FpPoly p) (k : Nat) :
    modMonic (frobeniusPowModMonic f modulus k) modulus =
      frobeniusPowModMonic f modulus k := by
  simpa [frobeniusPowModMonic_eq_powModMonic] using
    powModMonic_modMonic_self (base := f) (modulus := modulus) (n := p ^ k)

/-- Iterated Frobenius outputs stay in reduced remainder form. -/
theorem frobeniusPowModMonic_degree_lt (f modulus : FpPoly p) (k : Nat)
    (hmonic : HexPoly.DensePoly.Monic modulus) (hmodulus : modulus ≠ 0) :
    (frobeniusPowModMonic f modulus k).natDegree? = none ∨
      (frobeniusPowModMonic f modulus k).degree < modulus.degree := by
  simpa [frobeniusPowModMonic_eq_powModMonic] using
    powModMonic_degree_lt (base := f) (modulus := modulus) (n := p ^ k) hmonic hmodulus

end FpPoly

end HexPolyFp
