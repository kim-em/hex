import HexPolyZ.Content

/-!
# `HexPolyZ` — core conformance

Deterministic Lean-only conformance checks for the currently exported
`HexPolyZ` core/content surface. Every check elaborates as part of
`lake build HexPolyZ`, so regressions in congruence, coprimeness,
content, primitive-part normalization, or the executable Mignotte-bound
helpers fail CI immediately.

**Conformance contract for this slice:**

- **Oracle:** `none`. The `core` profile uses direct committed outputs
  and definitional coefficient/divisibility identities on small cases.
- **Mode:** `always`.
- **Covered operations:** `HexPolyZ.ZPoly.congr`,
  `HexPolyZ.ZPoly.coprimeModP`, `HexPolyZ.ZPoly.content`,
  `HexPolyZ.ZPoly.primitivePart`, `HexPolyZ.ZPoly.binomial`,
  `HexPolyZ.ZPoly.coeffTwoNormSq`, `HexPolyZ.ZPoly.coeffTwoNormCeil`,
  `HexPolyZ.ZPoly.mignotteBound`, `HexPolyZ.ZPoly.mignotteCoeffBound`,
  `HexPolyZ.ZPoly.mignotteUniformBound`.
- **Covered properties:**
  - congruence holds on committed equal/nonzero, zero, and
    trailing-zero-normalized examples;
  - committed modulus-`1` Bezout witnesses certify `coprimeModP` on
    representative nonzero, zero, and normalized-input examples;
  - `HexPoly.DensePoly.scaleInt (content f) (primitivePart f) = f` on
    committed typical, edge, and adversarial inputs;
  - nonzero committed primitive parts have content `1`.
  - `binomial n k = 0` on committed out-of-range inputs and remains
    symmetric on a representative interior case;
  - trailing-zero normalization preserves the committed coefficient
    `2`-norm and its exact ceiling;
  - `mignotteCoeffBound f k j = binomial k j * coeffTwoNormCeil f` and
    `mignotteUniformBound f k = mignotteCoeffBound f k (k / 2)` on
    committed inputs.
- **Covered edge cases:** zero polynomials for congruence, coprimeness,
  content, and primitive part; modulus `1` for the coprime-mod-`p`
  witness boundary; trailing-zero coefficient arrays that must
  normalize before the core/content predicates observe them; and
  out-of-range binomial indices / zero-degree Mignotte inputs.
-/

namespace HexPolyZ
namespace Conformance

namespace ZPoly

private def congrTypical : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[7, -3, 12]

private def congrAdversarial : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[6, 0, 0]

private def coprimeTypicalF : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[3, 4]

private def coprimeTypicalG : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[1, -2]

private def coprimeAdversarialF : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[5, 0, 0]

private def coprimeAdversarialG : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[0, 3, 0, 0]

private def contentTypical : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[6, -9, 3]

private def contentAdversarial : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[0, -12, 18, 0, 0]

private def mignotteTypical : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[2, -3, 5]

private def mignotteAdversarial : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[0, -5, 0, 12, 0, 0]

private def mignotteAdversarialNormalized : HexPolyZ.ZPoly :=
  HexPoly.DensePoly.ofArray #[0, -5, 0, 12]

/-! ## `ZPoly.congr` -/

example : HexPolyZ.ZPoly.congr congrTypical congrTypical 5 := by
  intro i
  simp [congrTypical, HexPoly.DensePoly.coeff]

example : HexPolyZ.ZPoly.congr (0 : HexPolyZ.ZPoly) 0 2 := by
  intro i
  simp [HexPoly.DensePoly.coeff]

example : HexPolyZ.ZPoly.congr congrAdversarial congrAdversarial 4 := by
  intro i
  simp [congrAdversarial, HexPoly.DensePoly.coeff]

/-! ## `ZPoly.coprimeModP`

For the Phase 3 `core` profile we use explicit modulus-`1` Bezout
certificates so the conformance checks exercise the existential witness
boundary directly without introducing external-oracle machinery. -/

example : HexPolyZ.ZPoly.coprimeModP coprimeTypicalF coprimeTypicalG 1 := by
  refine ⟨0, 0, ?_⟩
  intro i
  simp [coprimeTypicalF, coprimeTypicalG, HexPoly.DensePoly.coeff]

example : HexPolyZ.ZPoly.coprimeModP (0 : HexPolyZ.ZPoly) 0 1 := by
  refine ⟨0, 0, ?_⟩
  intro i
  simp [HexPoly.DensePoly.coeff]

example : HexPolyZ.ZPoly.coprimeModP coprimeAdversarialF coprimeAdversarialG 1 := by
  refine ⟨0, 0, ?_⟩
  intro i
  simp [coprimeAdversarialF, coprimeAdversarialG, HexPoly.DensePoly.coeff]

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

example :
    HexPoly.DensePoly.scaleInt (HexPolyZ.ZPoly.content contentTypical : Int)
      (HexPolyZ.ZPoly.primitivePart contentTypical) = contentTypical := by
  simpa [contentTypical] using HexPolyZ.ZPoly.scaleInt_content_primitivePart contentTypical

example :
    HexPoly.DensePoly.scaleInt (HexPolyZ.ZPoly.content (0 : HexPolyZ.ZPoly) : Int)
      (HexPolyZ.ZPoly.primitivePart (0 : HexPolyZ.ZPoly)) = (0 : HexPolyZ.ZPoly) := by
  simpa using HexPolyZ.ZPoly.scaleInt_content_primitivePart (0 : HexPolyZ.ZPoly)

example :
    HexPoly.DensePoly.scaleInt (HexPolyZ.ZPoly.content contentAdversarial : Int)
      (HexPolyZ.ZPoly.primitivePart contentAdversarial) = contentAdversarial := by
  simpa [contentAdversarial] using HexPolyZ.ZPoly.scaleInt_content_primitivePart contentAdversarial

#guard HexPolyZ.ZPoly.content (HexPolyZ.ZPoly.primitivePart contentTypical) = 1
#guard HexPolyZ.ZPoly.content (HexPolyZ.ZPoly.primitivePart contentAdversarial) = 1

/-! ## Executable Mignotte helpers -/

-- `#eval` refuses `DensePoly` values while `HexPoly.DensePoly.ofArray` carries `sorry`-backed proofs.

/-! ### `ZPoly.binomial` -/

/-- info: 10 -/
#guard_msgs in #eval HexPolyZ.ZPoly.binomial 5 2

/-- info: 0 -/
#guard_msgs in #eval HexPolyZ.ZPoly.binomial 0 3

/-- info: 0 -/
#guard_msgs in #eval HexPolyZ.ZPoly.binomial 4 5

#guard HexPolyZ.ZPoly.binomial 5 2 = HexPolyZ.ZPoly.binomial 5 3
#guard HexPolyZ.ZPoly.binomial 4 5 = 0

/-! ### `ZPoly.coeffTwoNormSq` and `ZPoly.coeffTwoNormCeil` -/

/-- info: 38 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.coeffTwoNormSq mignotteTypical

/-- info: 0 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.coeffTwoNormSq (0 : HexPolyZ.ZPoly)

/-- info: 169 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.coeffTwoNormSq mignotteAdversarial

/-- info: 7 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.coeffTwoNormCeil mignotteTypical

/-- info: 0 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.coeffTwoNormCeil (0 : HexPolyZ.ZPoly)

/-- info: 13 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.coeffTwoNormCeil mignotteAdversarial

#guard HexPolyZ.ZPoly.coeffTwoNormSq mignotteAdversarial =
  HexPolyZ.ZPoly.coeffTwoNormSq mignotteAdversarialNormalized
#guard HexPolyZ.ZPoly.coeffTwoNormCeil mignotteAdversarial =
  HexPolyZ.ZPoly.coeffTwoNormCeil mignotteAdversarialNormalized
#guard
  let ceil := HexPolyZ.ZPoly.coeffTwoNormCeil mignotteTypical
  let sq := HexPolyZ.ZPoly.coeffTwoNormSq mignotteTypical
  ceil ^ 2 >= sq && (ceil - 1) ^ 2 < sq

/-! ### `ZPoly.mignotteBound`, `ZPoly.mignotteCoeffBound`, and `ZPoly.mignotteUniformBound` -/

/-- info: 18.493242 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteBound mignotteTypical 3 1

/-- info: 0.000000 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteBound (0 : HexPolyZ.ZPoly) 5 2

/-- info: 78.000000 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteBound mignotteAdversarial 4 2

/-- info: 21 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteCoeffBound mignotteTypical 3 1

/-- info: 0 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteCoeffBound (0 : HexPolyZ.ZPoly) 5 2

/-- info: 78 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteCoeffBound mignotteAdversarial 4 2

/-- info: 42 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteUniformBound mignotteTypical 4

/-- info: 0 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteUniformBound (0 : HexPolyZ.ZPoly) 5

/-- info: 78 -/
#guard_msgs in #eval! HexPolyZ.ZPoly.mignotteUniformBound mignotteAdversarial 4

#guard
  HexPolyZ.ZPoly.mignotteCoeffBound mignotteTypical 3 1 =
    HexPolyZ.ZPoly.binomial 3 1 * HexPolyZ.ZPoly.coeffTwoNormCeil mignotteTypical
#guard
  HexPolyZ.ZPoly.mignotteCoeffBound mignotteAdversarial 4 2 =
    HexPolyZ.ZPoly.binomial 4 2 * HexPolyZ.ZPoly.coeffTwoNormCeil mignotteAdversarial
#guard
  HexPolyZ.ZPoly.mignotteUniformBound mignotteTypical 4 =
    HexPolyZ.ZPoly.mignotteCoeffBound mignotteTypical 4 (4 / 2)
#guard
  HexPolyZ.ZPoly.mignotteUniformBound mignotteAdversarial 4 =
    HexPolyZ.ZPoly.mignotteCoeffBound mignotteAdversarial 4 (4 / 2)

end ZPoly
end Conformance
end HexPolyZ
