import HexPoly.Eval
import HexPoly.Gcd

/-!
# `HexPoly` — core conformance

Deterministic Lean-only conformance checks for the `HexPoly` evaluation,
derivative, arithmetic, division, and GCD surface. Every check
elaborates as part of `lake build HexPoly`, so regressions in these
executable operations fail CI immediately.

**Conformance contract for this slice:**

- **Oracle:** `none`. The `core` profile for this slice uses direct
  committed outputs and algebraic identities on small instances.
- **Mode:** `always`.
- **Covered operations:** `HexPoly.DensePoly.eval`,
  `HexPoly.DensePoly.derivative`, `HexPoly.DensePoly.compose`,
  `HexPoly.DensePoly.add`, `HexPoly.DensePoly.sub`,
  `HexPoly.DensePoly.mul`, `HexPoly.DensePoly.divModMonic`,
  `HexPoly.DensePoly.gcd`, `HexPoly.DensePoly.xgcd`.
- **Covered properties:**
  - evaluation on committed inputs agrees with constant-term and
    zero-polynomial identities;
  - derivative on committed inputs handles constant and monomial cases
    with the expected coefficient shifts;
  - composition respects identity and zero-inner-polynomial laws on
    committed inputs;
  - `eval (p.compose q) x = eval p (eval q x)` on a committed example;
  - addition and multiplication normalize trailing-zero inputs, while
    subtraction cancels equal polynomials to zero;
  - monic division satisfies `divisor * quotient + remainder = dividend`
    on committed exact and inexact examples;
  - `xgcd` agrees with `gcd` and satisfies the Bezout identity on
    committed field-valued examples.
- **Covered edge cases:** zero polynomial, constant polynomial,
  monomials, and trailing-zero coefficient arrays that must normalize
  before arithmetic or composition; zero divisor handling in monic
  division; zero second argument and non-monic constant outputs in GCD.
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

private def addLeftTypical : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1, 2, 3]

private def addRightTypical : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[4, -2, 1]

private def addEdge : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[7]

private def addLeftAdversarial : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[2, 0, 3, 0, 0]

private def addRightAdversarial : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[-2, 1, -3]

private def mulLeftTypical : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1, 2]

private def mulRightTypical : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[3, 4]

private def mulLeftAdversarial : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1, 0, 1]

private def mulRightAdversarial : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1, -1]

private def oneIntPoly : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1]

private def divTypicalDividend : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[2, -3, 0, 1]

private def divTypicalDivisor : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[-1, 1]

private def divEdgeDividend : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[3, 0, 2]

private def divAdversarialDividend : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1, 0, -1, 0, 0]

private def divAdversarialDivisor : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray #[1, 1]

private def gcdTypicalF : HexPoly.DensePoly Rat :=
  HexPoly.DensePoly.ofArray #[(-1 : Rat), 0, 1]

private def gcdTypicalG : HexPoly.DensePoly Rat :=
  HexPoly.DensePoly.ofArray #[(-1 : Rat), 1]

private def gcdEdgeF : HexPoly.DensePoly Rat :=
  HexPoly.DensePoly.ofArray #[(-1 : Rat), 0, 1]

private def gcdAdversarialF : HexPoly.DensePoly Rat :=
  HexPoly.DensePoly.ofArray #[(1 : Rat), 0, 1]

private def gcdAdversarialG : HexPoly.DensePoly Rat :=
  HexPoly.DensePoly.ofArray #[(1 : Rat), 1]

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

/-! ## `DensePoly.add` and `DensePoly.sub` -/

/-- info: [5, 0, 4] -/
#guard_msgs in #eval! (addLeftTypical + addRightTypical).coeffs.toList

/-- info: [7] -/
#guard_msgs in #eval! ((0 : HexPoly.DensePoly Int) + addEdge).coeffs.toList

/-- info: [0, 1] -/
#guard_msgs in #eval! (addLeftAdversarial + addRightAdversarial).coeffs.toList

#guard (addLeftTypical + addRightTypical).coeffs.toList = [5, 0, 4]
#guard (addLeftTypical + addRightTypical).coeffs.toList =
         (addRightTypical + addLeftTypical).coeffs.toList
#guard ((0 : HexPoly.DensePoly Int) + addEdge).coeffs.toList = addEdge.coeffs.toList
#guard (addLeftAdversarial + addRightAdversarial).coeffs.toList = [0, 1]

/-- info: [-3, 4, 2] -/
#guard_msgs in #eval! (addLeftTypical - addRightTypical).coeffs.toList

/-- info: [] -/
#guard_msgs in #eval! (addEdge - addEdge).coeffs.toList

/-- info: [] -/
#guard_msgs in #eval!
  (addLeftAdversarial - HexPoly.DensePoly.ofArray #[2, 0, 3]).coeffs.toList

#guard (addLeftTypical - addRightTypical).coeffs.toList = [-3, 4, 2]
#guard (addEdge - addEdge).coeffs.toList = []
#guard (addLeftTypical - (0 : HexPoly.DensePoly Int)).coeffs.toList = addLeftTypical.coeffs.toList
#guard ((addLeftAdversarial - HexPoly.DensePoly.ofArray #[2, 0, 3]).coeffs.toList = [])

/-! ## `DensePoly.mul` -/

/-- info: [3, 10, 8] -/
#guard_msgs in #eval! (mulLeftTypical * mulRightTypical).coeffs.toList

/-- info: [] -/
#guard_msgs in #eval! (mulLeftTypical * (0 : HexPoly.DensePoly Int)).coeffs.toList

/-- info: [1, -1, 1, -1] -/
#guard_msgs in #eval! (mulLeftAdversarial * mulRightAdversarial).coeffs.toList

#guard (mulLeftTypical * mulRightTypical).coeffs.toList = [3, 10, 8]
#guard (mulLeftTypical * mulRightTypical).coeffs.toList =
         (mulRightTypical * mulLeftTypical).coeffs.toList
#guard (mulLeftTypical * (0 : HexPoly.DensePoly Int)).coeffs.toList = []
#guard (mulLeftAdversarial * mulRightAdversarial).coeffs.toList = [1, -1, 1, -1]
#guard (mulLeftAdversarial * oneIntPoly).coeffs.toList = mulLeftAdversarial.coeffs.toList

/-! ## `DensePoly.divModMonic` -/

/-- info: ([-2, 1, 1], []) -/
#guard_msgs in #eval!
  let qr := HexPoly.DensePoly.divModMonic divTypicalDividend divTypicalDivisor
  (qr.quotient.coeffs.toList, qr.remainder.coeffs.toList)

/-- info: ([], [3, 0, 2]) -/
#guard_msgs in #eval!
  let qr := HexPoly.DensePoly.divModMonic divEdgeDividend (0 : HexPoly.DensePoly Int)
  (qr.quotient.coeffs.toList, qr.remainder.coeffs.toList)

/-- info: ([1, -1], []) -/
#guard_msgs in #eval!
  let qr := HexPoly.DensePoly.divModMonic divAdversarialDividend divAdversarialDivisor
  (qr.quotient.coeffs.toList, qr.remainder.coeffs.toList)

#guard let qr := HexPoly.DensePoly.divModMonic divTypicalDividend divTypicalDivisor;
       (divTypicalDivisor * qr.quotient + qr.remainder).coeffs.toList = divTypicalDividend.coeffs.toList
#guard let qr := HexPoly.DensePoly.divModMonic divTypicalDividend divTypicalDivisor;
       qr.remainder.coeffs.size = 0 ∨ qr.remainder.degree < divTypicalDivisor.degree
#guard let qr := HexPoly.DensePoly.divModMonic divEdgeDividend (0 : HexPoly.DensePoly Int);
       qr.quotient.coeffs.toList = [] ∧ qr.remainder.coeffs.toList = divEdgeDividend.coeffs.toList
#guard let qr := HexPoly.DensePoly.divModMonic divAdversarialDividend divAdversarialDivisor;
       (divAdversarialDivisor * qr.quotient + qr.remainder).coeffs.toList =
         divAdversarialDividend.coeffs.toList

/-! ## `DensePoly.gcd` and `DensePoly.xgcd` -/

/-- info: [-1, 1] -/
#guard_msgs in #eval! (HexPoly.DensePoly.gcd gcdTypicalF gcdTypicalG).coeffs.toList

/-- info: [-1, 0, 1] -/
#guard_msgs in #eval! (HexPoly.DensePoly.gcd gcdEdgeF (0 : HexPoly.DensePoly Rat)).coeffs.toList

/-- info: [2] -/
#guard_msgs in #eval! (HexPoly.DensePoly.gcd gcdAdversarialF gcdAdversarialG).coeffs.toList

/-- info: ([-1, 1], [], [1]) -/
#guard_msgs in #eval!
  let r := HexPoly.DensePoly.xgcd gcdTypicalF gcdTypicalG
  (r.gcd.coeffs.toList, r.s.coeffs.toList, r.t.coeffs.toList)

/-- info: ([-1, 0, 1], [1], []) -/
#guard_msgs in #eval!
  let r := HexPoly.DensePoly.xgcd gcdEdgeF (0 : HexPoly.DensePoly Rat)
  (r.gcd.coeffs.toList, r.s.coeffs.toList, r.t.coeffs.toList)

/-- info: ([2], [1], [1, -1]) -/
#guard_msgs in #eval!
  let r := HexPoly.DensePoly.xgcd gcdAdversarialF gcdAdversarialG
  (r.gcd.coeffs.toList, r.s.coeffs.toList, r.t.coeffs.toList)

#guard let r := HexPoly.DensePoly.xgcd gcdTypicalF gcdTypicalG;
       r.gcd.coeffs.toList = (HexPoly.DensePoly.gcd gcdTypicalF gcdTypicalG).coeffs.toList
#guard let r := HexPoly.DensePoly.xgcd gcdTypicalF gcdTypicalG;
       (r.s * gcdTypicalF + r.t * gcdTypicalG).coeffs.toList = r.gcd.coeffs.toList
#guard let r := HexPoly.DensePoly.xgcd gcdEdgeF (0 : HexPoly.DensePoly Rat);
       r.gcd.coeffs.toList = (HexPoly.DensePoly.gcd gcdEdgeF 0).coeffs.toList
#guard let r := HexPoly.DensePoly.xgcd gcdEdgeF (0 : HexPoly.DensePoly Rat);
       (r.s * gcdEdgeF + r.t * (0 : HexPoly.DensePoly Rat)).coeffs.toList = r.gcd.coeffs.toList
#guard let r := HexPoly.DensePoly.xgcd gcdAdversarialF gcdAdversarialG;
       r.gcd.coeffs.toList = (HexPoly.DensePoly.gcd gcdAdversarialF gcdAdversarialG).coeffs.toList
#guard let r := HexPoly.DensePoly.xgcd gcdAdversarialF gcdAdversarialG;
       (r.s * gcdAdversarialF + r.t * gcdAdversarialG).coeffs.toList = r.gcd.coeffs.toList

end DensePoly
end Conformance
end HexPoly
