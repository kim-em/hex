import HexPoly.Eval

/-!
# `HexPoly` — core conformance (evaluation slice)

Deterministic Lean-only conformance checks for the `HexPoly` evaluation,
derivative, and composition surface. Every check elaborates as part of
`lake build HexPoly`, so regressions in these executable operations fail
CI immediately.

**Conformance contract for this slice:**

- **Oracle:** `none`. The `core` profile for this slice uses direct
  committed outputs and algebraic identities on small instances.
- **Mode:** `always`.
- **Covered operations:** `HexPoly.DensePoly.eval`,
  `HexPoly.DensePoly.derivative`, `HexPoly.DensePoly.compose`.
- **Covered properties:**
  - evaluation on committed inputs agrees with constant-term and
    zero-polynomial identities;
  - derivative on committed inputs handles constant and monomial cases
    with the expected coefficient shifts;
  - composition respects identity and zero-inner-polynomial laws on
    committed inputs;
  - `eval (p.compose q) x = eval p (eval q x)` on a committed example.
- **Covered edge cases:** zero polynomial, constant polynomial,
  monomials, and trailing-zero coefficient arrays that must normalize
  before evaluation or composition.
-/

namespace HexPoly
namespace Conformance

namespace DensePoly

private def evalTypical : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[3, -1, 2]

private def evalTrailing : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[2, 0, 3, 0, 0]

private def derivativeTypical : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[5, -3, 0, 2]

private def derivativeTrailing : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[0, 0, 4, 0, 0]

private def derivativeMonomial : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[0, 0, 0, 5]

private def composeOuterTypical : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1, 2, 1]

private def composeInnerTypical : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1, 1]

private def composeIdentity : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[0, 1, 0, 0]

private def composeZeroInner : HexPoly.DensePoly Int :=
  0

/-! ## `DensePoly.eval` -/

/-- info: 18 -/
#guard_msgs in #eval! HexPoly.DensePoly.eval evalTypical 3

/-- info: 0 -/
#guard_msgs in #eval! HexPoly.DensePoly.eval (0 : HexPoly.DensePoly Int) 5

/-- info: 14 -/
#guard_msgs in #eval! HexPoly.DensePoly.eval evalTrailing 2

#guard HexPoly.DensePoly.eval evalTypical 0 = evalTypical.coeff 0
#guard HexPoly.DensePoly.eval (HexPoly.DensePoly.ofArray #[7]) 10 = 7
#guard HexPoly.DensePoly.eval evalTrailing 1 = 5

/-! ## `DensePoly.derivative` -/

/-- info: [-3, 0, 6] -/
#guard_msgs in #eval! (HexPoly.DensePoly.derivative derivativeTypical).coeffs.toList

/-- info: [] -/
#guard_msgs in #eval! (HexPoly.DensePoly.derivative (HexPoly.DensePoly.ofArray #[7])).coeffs.toList

/-- info: [0, 8] -/
#guard_msgs in #eval! (HexPoly.DensePoly.derivative derivativeTrailing).coeffs.toList

#guard (HexPoly.DensePoly.derivative (0 : HexPoly.DensePoly Int)).coeffs.toList = []
#guard (HexPoly.DensePoly.derivative derivativeMonomial).coeffs.toList = [0, 0, 15]
#guard (HexPoly.DensePoly.derivative (HexPoly.DensePoly.ofArray #[4, -2])).coeffs.toList = [-2]

/-! ## `DensePoly.compose` -/

/-- info: [4, 4, 1] -/
#guard_msgs in #eval! (HexPoly.DensePoly.compose composeOuterTypical composeInnerTypical).coeffs.toList

/-- info: [] -/
#guard_msgs in #eval! (HexPoly.DensePoly.compose (0 : HexPoly.DensePoly Int)
  (HexPoly.DensePoly.ofArray #[3, 4])).coeffs.toList

/-- info: [2, 0, 3] -/
#guard_msgs in #eval! (HexPoly.DensePoly.compose evalTrailing composeIdentity).coeffs.toList

#guard (HexPoly.DensePoly.compose evalTrailing composeIdentity).coeffs.toList = evalTrailing.coeffs.toList
#guard (HexPoly.DensePoly.compose composeOuterTypical composeZeroInner).coeffs.toList = [1]
#guard HexPoly.DensePoly.eval (HexPoly.DensePoly.compose composeOuterTypical composeInnerTypical) 2 =
         HexPoly.DensePoly.eval composeOuterTypical
           (HexPoly.DensePoly.eval composeInnerTypical 2)

end DensePoly
end Conformance
end HexPoly
