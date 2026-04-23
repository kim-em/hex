import HexPolyMathlib.Gcd

/-!
# `HexPolyMathlib` -- core conformance

Deterministic Lean-only conformance checks for the dense-polynomial
bridge into Mathlib. These checks exercise the existing conversion,
equivalence, and gcd/xgcd correspondence surface on committed tiny
`Rat` examples, so regressions fail during `lake build HexPolyMathlib`.

**Conformance contract for this slice:**

- **Oracle:** `none`.
- **Mode:** `always`.
- **Covered operations:** `HexPolyMathlib.DensePoly.toPolynomial`,
  `HexPolyMathlib.DensePoly.ofPolynomial`,
  `HexPolyMathlib.DensePoly.equiv`,
  `HexPolyMathlib.DensePoly.toPolynomial_gcd`,
  `HexPolyMathlib.DensePoly.ofPolynomial_gcd`,
  `HexPolyMathlib.DensePoly.toPolynomial_xgcd_gcd`,
  `HexPolyMathlib.DensePoly.toPolynomial_xgcd_bezout`.
- **Covered properties:**
  - dense-to-Mathlib and Mathlib-to-dense round trips hold on
    committed typical, edge, and adversarial examples;
  - the bridge equivalence preserves committed addition and
    multiplication examples, including a trailing-zero-normalized input;
  - executable dense gcd agrees with Mathlib gcd after conversion, and
    converting Mathlib gcd back to dense form recovers the executable
    gcd on committed examples;
  - the gcd packaged by `xgcd` agrees with Mathlib gcd, and the mapped
    Bezout coefficients satisfy the expected identity on committed
    examples.
- **Covered edge cases:** the zero polynomial, degree-0 constant
  polynomials, and trailing-zero coefficient arrays that normalize
  before crossing the bridge.
-/

namespace HexPolyMathlib
namespace Conformance

open Polynomial
open HexPolyMathlib.DensePoly

noncomputable section

private def denseRat (xs : List Rat) : HexPoly.DensePoly Rat :=
  HexPoly.DensePoly.ofArray xs.toArray

private def denseCoeffs (p : HexPoly.DensePoly Rat) : List Rat :=
  p.coeffs.toList

private def polynomialCoeffs (n : Nat) (p : Rat[X]) : List Rat :=
  (List.range (n + 1)).map p.coeff

private def denseTypical : HexPoly.DensePoly Rat :=
  denseRat [1, -2, 3]

private def denseEdge : HexPoly.DensePoly Rat :=
  0

private def denseAdversarial : HexPoly.DensePoly Rat :=
  denseRat [5, 0, 0]

private def polynomialTypical : Rat[X] :=
  C (1 : Rat) + C (-2 : Rat) * X + C (3 : Rat) * X ^ 2

private def polynomialEdge : Rat[X] :=
  0

private def polynomialAdversarial : Rat[X] :=
  C (5 : Rat)

private def addTypicalLeft : HexPoly.DensePoly Rat :=
  denseRat [1, -1, 2]

private def addTypicalRight : HexPoly.DensePoly Rat :=
  denseRat [3, 0, 1]

private def mulTypicalLeft : HexPoly.DensePoly Rat :=
  denseRat [2, 3, 1]

private def mulTypicalRight : HexPoly.DensePoly Rat :=
  denseRat [1, 1]

private def gcdTypicalLeft : HexPoly.DensePoly Rat :=
  denseRat [2, 3, 1]

private def gcdTypicalRight : HexPoly.DensePoly Rat :=
  denseRat [3, 4, 1]

private def gcdEdgeLeft : HexPoly.DensePoly Rat :=
  0

private def gcdEdgeRight : HexPoly.DensePoly Rat :=
  denseRat [1, 1]

private def gcdAdversarialLeft : HexPoly.DensePoly Rat :=
  denseRat [2, 4, 2, 0, 0]

private def gcdAdversarialRight : HexPoly.DensePoly Rat :=
  denseRat [2, 2, 0]

private def polynomialGcdTypicalLeft : Rat[X] :=
  C (2 : Rat) + C (3 : Rat) * X + X ^ 2

private def polynomialGcdTypicalRight : Rat[X] :=
  C (3 : Rat) + C (4 : Rat) * X + X ^ 2

private def polynomialGcdEdgeLeft : Rat[X] :=
  0

private def polynomialGcdEdgeRight : Rat[X] :=
  C (1 : Rat) + X

private def polynomialGcdAdversarialLeft : Rat[X] :=
  C (2 : Rat) + C (4 : Rat) * X + C (2 : Rat) * X ^ 2

private def polynomialGcdAdversarialRight : Rat[X] :=
  C (2 : Rat) + C (2 : Rat) * X

/-! ## Conversion spot checks -/

example := ofPolynomial_toPolynomial denseTypical
example := ofPolynomial_toPolynomial denseEdge
example := ofPolynomial_toPolynomial denseAdversarial

example := toPolynomial_ofPolynomial polynomialTypical
example := toPolynomial_ofPolynomial polynomialEdge
example := toPolynomial_ofPolynomial polynomialAdversarial

/-! ## Ring-equivalence checks -/

example :
    equiv (addTypicalLeft + addTypicalRight) =
      equiv addTypicalLeft + equiv addTypicalRight := by
  exact equiv.map_add addTypicalLeft addTypicalRight

example :
    equiv (denseEdge + addTypicalRight) =
      equiv denseEdge + equiv addTypicalRight := by
  exact equiv.map_add denseEdge addTypicalRight

example :
    equiv (denseAdversarial + denseEdge) =
      equiv denseAdversarial + equiv denseEdge := by
  exact equiv.map_add denseAdversarial denseEdge

example :
    equiv (mulTypicalLeft * mulTypicalRight) =
      equiv mulTypicalLeft * equiv mulTypicalRight := by
  exact equiv.map_mul mulTypicalLeft mulTypicalRight

example :
    equiv (denseEdge * mulTypicalRight) =
      equiv denseEdge * equiv mulTypicalRight := by
  exact equiv.map_mul denseEdge mulTypicalRight

example :
    equiv (denseAdversarial * denseRat [0, 1]) =
      equiv denseAdversarial * equiv (denseRat [0, 1]) := by
  exact equiv.map_mul denseAdversarial (denseRat [0, 1])

/-! ## GCD bridge checks -/

example := toPolynomial_gcd gcdTypicalLeft gcdTypicalRight
example := toPolynomial_gcd gcdEdgeLeft gcdEdgeRight
example := toPolynomial_gcd gcdAdversarialLeft gcdAdversarialRight

example := ofPolynomial_gcd polynomialGcdTypicalLeft polynomialGcdTypicalRight
example := ofPolynomial_gcd polynomialGcdEdgeLeft polynomialGcdEdgeRight
example := ofPolynomial_gcd polynomialGcdAdversarialLeft polynomialGcdAdversarialRight

/-! ## Extended-GCD bridge checks -/

example := toPolynomial_xgcd_gcd gcdTypicalLeft gcdTypicalRight
example := toPolynomial_xgcd_gcd gcdEdgeLeft gcdEdgeRight
example := toPolynomial_xgcd_gcd gcdAdversarialLeft gcdAdversarialRight

example := toPolynomial_xgcd_bezout gcdTypicalLeft gcdTypicalRight
example := toPolynomial_xgcd_bezout gcdEdgeLeft gcdEdgeRight
example := toPolynomial_xgcd_bezout gcdAdversarialLeft gcdAdversarialRight

end
end Conformance
end HexPolyMathlib
