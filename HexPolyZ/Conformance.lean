import HexPolyZ.Content

/-!
# `HexPolyZ` — core/content conformance

Deterministic Lean-only conformance checks for the currently exported
`HexPolyZ` surface. Every check elaborates as part of `lake build
HexPolyZ`, so regressions in the integer-polynomial scaffolding fail CI
immediately.

**Conformance contract for this slice:**

- **Oracle:** `none`. The `core` profile for this slice uses committed
  outputs and structural identities on small fixtures only.
- **Mode:** `always`.
- **Covered operations:** `HexPolyZ.ZPoly.congr`,
  `HexPolyZ.ZPoly.coprimeModP`, `HexPolyZ.ZPoly.content`,
  `HexPolyZ.ZPoly.primitivePart`.
- **Covered properties:**
  - coefficientwise congruence checks concrete divisibility residues on
    committed fixtures, including normalized trailing-zero inputs;
  - committed Bézout witnesses for `coprimeModP` reduce to a polynomial
    congruent to `1` modulo the requested modulus;
  - `scaleInt (content f) (primitivePart f) = f` on committed typical,
    edge, and adversarial fixtures;
  - `content (primitivePart f) = 1` on committed nonzero typical and
    adversarial fixtures.
- **Covered edge cases:** zero polynomial for content and primitive
  part; modulus `1` congruence; committed trailing-zero coefficient
  inputs that must normalize before congruence/content checks; and unit
  witness cases for `coprimeModP`.
-/

namespace HexPolyZ
namespace Conformance
namespace ZPoly

private def supportBelow (f : HexPolyZ.ZPoly) (bound : Nat) : Bool :=
  f.coeffs.size ≤ bound

private def congrUpTo (f g : HexPolyZ.ZPoly) (m bound : Nat) : Bool :=
  (List.range bound).all fun i =>
    ((f.coeff i - g.coeff i) % (m : Int)) == 0

private def coprimeWitnessCheck
    (f g s t : HexPolyZ.ZPoly) (p bound : Nat) : Bool :=
  congrUpTo (s * f + t * g) (HexPoly.DensePoly.ofArray #[1]) p bound

private def congrTypicalL : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[1, 5, -2]

private def congrTypicalR : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[4, 2, 1]

private def congrEdgeR : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[7, -3]

private def congrAdversarialL : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[3, 0, -6, 0, 0]

private def congrAdversarialR : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[-1, 0, -2]

private def coprimeTypicalF : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[2]

private def coprimeTypicalG : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[3]

private def coprimeTypicalS : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[-1]

private def coprimeTypicalT : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[1]

private def coprimeEdgeG : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[1]

private def coprimeEdgeT : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[1]

private def coprimeAdversarialF : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[2, 0, 0]

private def coprimeAdversarialG : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[5]

private def coprimeAdversarialS : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[1]

private def coprimeAdversarialT : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[1]

private def contentTypical : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[6, -9, 3]

private def contentAdversarial : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[0, -12, 18, 0, 0]

/-! ## `ZPoly.congr` -/

#guard supportBelow congrTypicalL 3
#guard supportBelow congrTypicalR 3
#guard supportBelow (0 : HexPolyZ.ZPoly) 2
#guard supportBelow congrEdgeR 2
#guard supportBelow congrAdversarialL 3
#guard supportBelow congrAdversarialR 3

/-- info: [0, 0, 0] -/
#guard_msgs in #eval! (List.range 3).map fun i =>
  ((congrTypicalL.coeff i - congrTypicalR.coeff i) % (3 : Int))

/-- info: [0, 0] -/
#guard_msgs in #eval! (List.range 2).map fun i =>
  (((0 : HexPolyZ.ZPoly).coeff i - congrEdgeR.coeff i) % (1 : Int))

/-- info: [0, 0, 0] -/
#guard_msgs in #eval! (List.range 3).map fun i =>
  ((congrAdversarialL.coeff i - congrAdversarialR.coeff i) % (4 : Int))

#guard congrUpTo congrTypicalL congrTypicalR 3 3
#guard congrUpTo (0 : HexPolyZ.ZPoly) congrEdgeR 1 2
#guard congrUpTo congrAdversarialL congrAdversarialR 4 3

/-! ## `ZPoly.coprimeModP` witness checks -/

#guard supportBelow coprimeTypicalF 1
#guard supportBelow coprimeTypicalG 1
#guard supportBelow coprimeTypicalS 1
#guard supportBelow coprimeTypicalT 1
#guard supportBelow (0 : HexPolyZ.ZPoly) 1
#guard supportBelow coprimeEdgeG 1
#guard supportBelow coprimeEdgeT 1
#guard supportBelow coprimeAdversarialF 1
#guard supportBelow coprimeAdversarialG 1
#guard supportBelow coprimeAdversarialS 1
#guard supportBelow coprimeAdversarialT 1

/-- info: [1] -/
#guard_msgs in #eval! ((coprimeTypicalS * coprimeTypicalF +
  coprimeTypicalT * coprimeTypicalG).coeffs.toList)

/-- info: [1] -/
#guard_msgs in #eval! (((0 : HexPolyZ.ZPoly) * (0 : HexPolyZ.ZPoly) +
  coprimeEdgeT * coprimeEdgeG).coeffs.toList)

/-- info: [7] -/
#guard_msgs in #eval! ((coprimeAdversarialS * coprimeAdversarialF +
  coprimeAdversarialT * coprimeAdversarialG).coeffs.toList)

#guard coprimeWitnessCheck coprimeTypicalF coprimeTypicalG
  coprimeTypicalS coprimeTypicalT 5 1
#guard coprimeWitnessCheck (0 : HexPolyZ.ZPoly) coprimeEdgeG
  (0 : HexPolyZ.ZPoly) coprimeEdgeT 7 1
#guard coprimeWitnessCheck coprimeAdversarialF coprimeAdversarialG
  coprimeAdversarialS coprimeAdversarialT 3 1

/-! ## `ZPoly.content` and `ZPoly.primitivePart` -/

/-- info: 3 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.content contentTypical

/-- info: 0 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.content (0 : HexPolyZ.ZPoly)

/-- info: 6 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.content contentAdversarial

#guard HexPolyZ.ZPoly.content contentTypical = 3
#guard HexPolyZ.ZPoly.content (0 : HexPolyZ.ZPoly) = 0
#guard HexPolyZ.ZPoly.content contentAdversarial = 6

/-- info: [2, -3, 1] -/
#guard_msgs in #eval! (HexPolyZ.ZPoly.primitivePart contentTypical).coeffs.toList

/-- info: [] -/
#guard_msgs in #eval! (HexPolyZ.ZPoly.primitivePart (0 : HexPolyZ.ZPoly)).coeffs.toList

/-- info: [0, -2, 3] -/
#guard_msgs in #eval! (HexPolyZ.ZPoly.primitivePart contentAdversarial).coeffs.toList

#guard (HexPolyZ.ZPoly.primitivePart contentTypical).coeffs.toList = [2, -3, 1]
#guard (HexPolyZ.ZPoly.primitivePart (0 : HexPolyZ.ZPoly)).coeffs.toList = []
#guard (HexPolyZ.ZPoly.primitivePart contentAdversarial).coeffs.toList = [0, -2, 3]

/-! ## `ZPoly.scaleInt_content_primitivePart` and
`ZPoly.content_primitivePart_of_ne_zero` -/

#guard (HexPoly.DensePoly.scaleInt (HexPolyZ.ZPoly.content contentTypical : Int)
          (HexPolyZ.ZPoly.primitivePart contentTypical)).coeffs.toList =
         contentTypical.coeffs.toList
#guard (HexPoly.DensePoly.scaleInt (HexPolyZ.ZPoly.content (0 : HexPolyZ.ZPoly) : Int)
          (HexPolyZ.ZPoly.primitivePart (0 : HexPolyZ.ZPoly))).coeffs.toList = []
#guard (HexPoly.DensePoly.scaleInt (HexPolyZ.ZPoly.content contentAdversarial : Int)
          (HexPolyZ.ZPoly.primitivePart contentAdversarial)).coeffs.toList =
         contentAdversarial.coeffs.toList

#guard HexPolyZ.ZPoly.content (HexPolyZ.ZPoly.primitivePart contentTypical) = 1
#guard HexPolyZ.ZPoly.content (HexPolyZ.ZPoly.primitivePart contentAdversarial) = 1

end ZPoly
end Conformance
end HexPolyZ
