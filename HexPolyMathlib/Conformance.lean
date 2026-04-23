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
  - the bridge equivalence preserves committed addition,
    multiplication, negation, subtraction, and exponentiation examples,
    including trailing-zero-normalized inputs;
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
  toPolynomial denseTypical

private def polynomialEdge : Rat[X] :=
  toPolynomial denseEdge

private def polynomialAdversarial : Rat[X] :=
  toPolynomial denseAdversarial

private def addTypicalLeft : HexPoly.DensePoly Rat :=
  denseRat [1, -1, 2]

private def addTypicalRight : HexPoly.DensePoly Rat :=
  denseRat [3, 0, 1]

private def addAdversarialLeft : HexPoly.DensePoly Rat :=
  denseRat [5, 0, 0]

private def addAdversarialRight : HexPoly.DensePoly Rat :=
  denseRat [0, 1]

private def mulTypicalLeft : HexPoly.DensePoly Rat :=
  denseRat [2, 3, 1]

private def mulTypicalRight : HexPoly.DensePoly Rat :=
  denseRat [1, 1]

private def subAdversarialLeft : HexPoly.DensePoly Rat :=
  denseRat [7, 0, 0]

private def subAdversarialRight : HexPoly.DensePoly Rat :=
  denseRat [2]

private def powTypical : HexPoly.DensePoly Rat :=
  denseRat [1, 1]

private def powAdversarial : HexPoly.DensePoly Rat :=
  denseRat [-1, 1]

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
  toPolynomial gcdTypicalLeft

private def polynomialGcdTypicalRight : Rat[X] :=
  toPolynomial gcdTypicalRight

private def polynomialGcdEdgeLeft : Rat[X] :=
  toPolynomial gcdEdgeLeft

private def polynomialGcdEdgeRight : Rat[X] :=
  toPolynomial gcdEdgeRight

private def polynomialGcdAdversarialLeft : Rat[X] :=
  toPolynomial gcdAdversarialLeft

private def polynomialGcdAdversarialRight : Rat[X] :=
  toPolynomial gcdAdversarialRight

-- `#eval` must bypass `DensePoly`'s sorry-bearing proof fields while
-- still evaluating the executable dense side of the bridge.

/-! ## Conversion spot checks -/

example :
    denseCoeffs (ofPolynomial polynomialTypical) = denseCoeffs denseTypical := by
  simpa [polynomialTypical] using congrArg denseCoeffs (ofPolynomial_toPolynomial denseTypical)

example :
    denseCoeffs (ofPolynomial polynomialEdge) = denseCoeffs denseEdge := by
  simpa [polynomialEdge] using congrArg denseCoeffs (ofPolynomial_toPolynomial denseEdge)

example :
    denseCoeffs (ofPolynomial polynomialAdversarial) = denseCoeffs denseAdversarial := by
  simpa [polynomialAdversarial] using congrArg denseCoeffs (ofPolynomial_toPolynomial denseAdversarial)

example :
    polynomialCoeffs 2 (toPolynomial (ofPolynomial polynomialTypical)) =
      polynomialCoeffs 2 polynomialTypical := by
  simpa using congrArg (polynomialCoeffs 2) (toPolynomial_ofPolynomial polynomialTypical)

example :
    polynomialCoeffs 0 (toPolynomial (ofPolynomial polynomialEdge)) =
      polynomialCoeffs 0 polynomialEdge := by
  simpa using congrArg (polynomialCoeffs 0) (toPolynomial_ofPolynomial polynomialEdge)

example :
    polynomialCoeffs 0 (toPolynomial (ofPolynomial polynomialAdversarial)) =
      polynomialCoeffs 0 polynomialAdversarial := by
  simpa using congrArg (polynomialCoeffs 0) (toPolynomial_ofPolynomial polynomialAdversarial)

/-! ## Ring-equivalence checks -/

/-- info: [4, -1, 3] -/
#guard_msgs in
#eval! denseCoeffs (addTypicalLeft + addTypicalRight)

/-- info: [3, 0, 1] -/
#guard_msgs in
#eval! denseCoeffs (denseEdge + addTypicalRight)

/-- info: [5, 1] -/
#guard_msgs in
#eval! denseCoeffs (addAdversarialLeft + addAdversarialRight)

example :
    equiv (addTypicalLeft + addTypicalRight) =
      equiv addTypicalLeft + equiv addTypicalRight := by
  simpa using equiv.map_add addTypicalLeft addTypicalRight

example :
    equiv (denseEdge + addTypicalRight) =
      equiv denseEdge + equiv addTypicalRight := by
  simpa using equiv.map_add denseEdge addTypicalRight

example :
    equiv (addAdversarialLeft + addAdversarialRight) =
      equiv addAdversarialLeft + equiv addAdversarialRight := by
  simpa using equiv.map_add addAdversarialLeft addAdversarialRight

/-- info: [2, 5, 4, 1] -/
#guard_msgs in
#eval! denseCoeffs (mulTypicalLeft * mulTypicalRight)

/-- info: [] -/
#guard_msgs in
#eval! denseCoeffs (denseEdge * mulTypicalRight)

/-- info: [0, 5] -/
#guard_msgs in
#eval! denseCoeffs (denseAdversarial * denseRat [0, 1])

example :
    equiv (mulTypicalLeft * mulTypicalRight) =
      equiv mulTypicalLeft * equiv mulTypicalRight := by
  simpa using equiv.map_mul mulTypicalLeft mulTypicalRight

example :
    equiv (denseEdge * mulTypicalRight) =
      equiv denseEdge * equiv mulTypicalRight := by
  simpa using equiv.map_mul denseEdge mulTypicalRight

example :
    equiv (denseAdversarial * denseRat [0, 1]) =
      equiv denseAdversarial * equiv (denseRat [0, 1]) := by
  simpa using equiv.map_mul denseAdversarial (denseRat [0, 1])

/-- info: [-1, 2, -3] -/
#guard_msgs in
#eval! denseCoeffs (-denseTypical)

/-- info: [] -/
#guard_msgs in
#eval! denseCoeffs (-denseEdge)

/-- info: [-5] -/
#guard_msgs in
#eval! denseCoeffs (-denseAdversarial)

example : equiv (-denseTypical) = -equiv denseTypical := by
  simpa using equiv.map_neg denseTypical

example : equiv (-denseEdge) = -equiv denseEdge := by
  simpa using equiv.map_neg denseEdge

example : equiv (-denseAdversarial) = -equiv denseAdversarial := by
  simpa using equiv.map_neg denseAdversarial

/-- info: [-2, -1, 1] -/
#guard_msgs in
#eval! denseCoeffs (addTypicalLeft - addTypicalRight)

/-- info: [-3, 0, -1] -/
#guard_msgs in
#eval! denseCoeffs (denseEdge - addTypicalRight)

/-- info: [5] -/
#guard_msgs in
#eval! denseCoeffs (subAdversarialLeft - subAdversarialRight)

example :
    equiv (addTypicalLeft - addTypicalRight) =
      equiv addTypicalLeft - equiv addTypicalRight := by
  simpa using equiv.map_sub addTypicalLeft addTypicalRight

example :
    equiv (denseEdge - addTypicalRight) =
      equiv denseEdge - equiv addTypicalRight := by
  simpa using equiv.map_sub denseEdge addTypicalRight

example :
    equiv (subAdversarialLeft - subAdversarialRight) =
      equiv subAdversarialLeft - equiv subAdversarialRight := by
  simpa using equiv.map_sub subAdversarialLeft subAdversarialRight

/-- info: [1, 3, 3, 1] -/
#guard_msgs in
#eval! denseCoeffs (powTypical * powTypical * powTypical)

/-- info: [1] -/
#guard_msgs in
#eval! denseCoeffs (denseRat [1])

/-- info: [1, -2, 1] -/
#guard_msgs in
#eval! denseCoeffs (powAdversarial * powAdversarial)

example : equiv (powTypical ^ 3) = equiv powTypical ^ 3 := by
  simpa using equiv.map_pow powTypical 3

example : equiv (denseEdge ^ 0) = equiv denseEdge ^ 0 := by
  simpa using equiv.map_pow denseEdge 0

example : equiv (powAdversarial ^ 2) = equiv powAdversarial ^ 2 := by
  simpa using equiv.map_pow powAdversarial 2

/-! ## GCD bridge checks -/

/-- info: [-1, -1] -/
#guard_msgs in
#eval! denseCoeffs (HexPoly.DensePoly.gcd gcdTypicalLeft gcdTypicalRight)

/-- info: [1, 1] -/
#guard_msgs in
#eval! denseCoeffs (HexPoly.DensePoly.gcd gcdEdgeLeft gcdEdgeRight)

/-- info: [2, 2] -/
#guard_msgs in
#eval! denseCoeffs (HexPoly.DensePoly.gcd gcdAdversarialLeft gcdAdversarialRight)

example := toPolynomial_gcd gcdTypicalLeft gcdTypicalRight
example := toPolynomial_gcd gcdEdgeLeft gcdEdgeRight
example := toPolynomial_gcd gcdAdversarialLeft gcdAdversarialRight

example := ofPolynomial_gcd polynomialGcdTypicalLeft polynomialGcdTypicalRight
example := ofPolynomial_gcd polynomialGcdEdgeLeft polynomialGcdEdgeRight
example := ofPolynomial_gcd polynomialGcdAdversarialLeft polynomialGcdAdversarialRight

/-! ## Extended-GCD bridge checks -/

/-- info: [-1, -1] -/
#guard_msgs in
#eval! denseCoeffs (HexPoly.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).gcd

/-- info: [1, 1] -/
#guard_msgs in
#eval! denseCoeffs (HexPoly.DensePoly.xgcd gcdEdgeLeft gcdEdgeRight).gcd

/-- info: [2, 2] -/
#guard_msgs in
#eval! denseCoeffs (HexPoly.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).gcd

example := toPolynomial_xgcd_gcd gcdTypicalLeft gcdTypicalRight
example := toPolynomial_xgcd_gcd gcdEdgeLeft gcdEdgeRight
example := toPolynomial_xgcd_gcd gcdAdversarialLeft gcdAdversarialRight

#guard
  denseCoeffs
      ((HexPoly.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).s * gcdTypicalLeft +
        (HexPoly.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).t * gcdTypicalRight) =
    denseCoeffs (HexPoly.DensePoly.xgcd gcdTypicalLeft gcdTypicalRight).gcd
#guard
  denseCoeffs
      ((HexPoly.DensePoly.xgcd gcdEdgeLeft gcdEdgeRight).s * gcdEdgeLeft +
        (HexPoly.DensePoly.xgcd gcdEdgeLeft gcdEdgeRight).t * gcdEdgeRight) =
    denseCoeffs (HexPoly.DensePoly.xgcd gcdEdgeLeft gcdEdgeRight).gcd
#guard
  denseCoeffs
      ((HexPoly.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).s * gcdAdversarialLeft +
        (HexPoly.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).t * gcdAdversarialRight) =
    denseCoeffs (HexPoly.DensePoly.xgcd gcdAdversarialLeft gcdAdversarialRight).gcd

example := toPolynomial_xgcd_bezout gcdTypicalLeft gcdTypicalRight
example := toPolynomial_xgcd_bezout gcdEdgeLeft gcdEdgeRight
example := toPolynomial_xgcd_bezout gcdAdversarialLeft gcdAdversarialRight

end
end Conformance
end HexPolyMathlib
