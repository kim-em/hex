import HexPolyZ.Mignotte

/-!
Core conformance checks for the `hex-poly-z` integer-polynomial surface.

Oracle: none for the core profile; python-flint/Sage cross-checks are deferred
to external oracle profiles.
Mode: always
Covered operations:
- `ZPoly` as the integer specialization of `DensePoly`
- coefficientwise modular congruence via `ZPoly.congr`
- Bezout-style modular coprimality via `ZPoly.coprimeModP`
- `content`, `primitivePart`, `Primitive`, and primitive square-free
  decomposition
- Mignotte helpers: `binom`, `floorSqrt`, `ceilSqrt`, `coeffNormSq`,
  `coeffL2NormBound`, and `mignotteCoeffBound`
Covered properties:
- normalized `ZPoly` values erase trailing zero coefficients while preserving
  internal zeros
- committed congruence fixtures have all checked coefficient differences
  divisible by the modulus
- committed coprimality witnesses reconstruct `1` modulo `p` on checked
  coefficients
- `content * primitivePart` reconstructs committed integer polynomials
- primitive-part fixtures with nonzero content have content `1`
- primitive square-free decomposition removes repeated rational factors after
  primitive-part extraction
- Mignotte coefficient bounds equal `binom k j * coeffL2NormBound f`
Covered edge cases:
- zero polynomials and all-zero coefficient arrays
- trailing-zero and internal-zero polynomial representations
- modulus `1` congruence and out-of-support coefficient checks
- already primitive and nontrivial-content integer polynomials
- powers of `X`, repeated factors, and nontrivial content before square-free
  normalization
- square-root inputs `0`, nonsquares, and one-below-square adversarial values
- binomial requests with `k = 0` and `k > n`
-/

namespace Hex

namespace ZPoly

private def zpolyTypical : ZPoly := DensePoly.ofCoeffs #[3, 0, -2]
private def zpolyEdge : ZPoly := DensePoly.ofCoeffs #[0, 0, 0]
private def zpolyAdversarial : ZPoly := DensePoly.ofCoeffs #[0, 5, 0, -7, 0, 0]

private def congrTypicalLeft : ZPoly := DensePoly.ofCoeffs #[7, -3, 11]
private def congrTypicalRight : ZPoly := DensePoly.ofCoeffs #[2, 12, -4]
private def congrEdgeLeft : ZPoly := DensePoly.ofCoeffs #[4, 0, -9]
private def congrEdgeRight : ZPoly := DensePoly.ofCoeffs #[-2, 13, 5]
private def congrAdversarialLeft : ZPoly := DensePoly.ofCoeffs #[0, 8, 0, -6]
private def congrAdversarialRight : ZPoly := DensePoly.ofCoeffs #[0, -4, 0, 18]

private def congrAt (f g : ZPoly) (m i : Nat) : Bool :=
  ((f.coeff i - g.coeff i) % (m : Int)) == 0

private def congrOn (f g : ZPoly) (m bound : Nat) : Bool :=
  (List.range bound).all (fun i => congrAt f g m i)

private def coprimeTypicalF : ZPoly := DensePoly.ofCoeffs #[1, 1]
private def coprimeTypicalG : ZPoly := DensePoly.ofCoeffs #[2, 1]
private def coprimeTypicalS : ZPoly := DensePoly.ofCoeffs #[-1]
private def coprimeTypicalT : ZPoly := DensePoly.ofCoeffs #[1]

private def coprimeEdgeF : ZPoly := 0
private def coprimeEdgeG : ZPoly := 1
private def coprimeEdgeS : ZPoly := 0
private def coprimeEdgeT : ZPoly := 1

private def coprimeAdversarialF : ZPoly := DensePoly.ofCoeffs #[3, 0, 1]
private def coprimeAdversarialG : ZPoly := DensePoly.ofCoeffs #[2]
private def coprimeAdversarialS : ZPoly := 0
private def coprimeAdversarialT : ZPoly := DensePoly.ofCoeffs #[2]

private def bezoutCongrOn (s t f g : ZPoly) (p bound : Nat) : Bool :=
  congrOn (s * f + t * g) 1 p bound

private def contentZero : ZPoly := DensePoly.ofCoeffs #[0, 0, 0]
private def contentPrimitive : ZPoly := DensePoly.ofCoeffs #[1, -2, 3]
private def contentNontrivial : ZPoly := DensePoly.ofCoeffs #[-6, 0, 12]
private def contentNontrivialPrimitive : ZPoly := DensePoly.ofCoeffs #[-1, 0, 2]
private def contentAdversarial : ZPoly := DensePoly.ofCoeffs #[-14, 21, 0, -7, 0, 0]
private def squareFreeRepeated : ZPoly := DensePoly.ofCoeffs #[1, -2, 1]
private def squareFreeWithContent : ZPoly := DensePoly.ofCoeffs #[2, -4, 2]
private def squareFreePowerOfX : ZPoly := DensePoly.ofCoeffs #[0, 0, 1]
private def squareFreeAlreadyCore : ZPoly := DensePoly.ofCoeffs #[-1, 0, 1]
private def squareFreeNegativeConstant : ZPoly := DensePoly.ofCoeffs #[-2]

#guard zpolyTypical.toArray.toList = [3, 0, -2]
#guard zpolyEdge = (0 : ZPoly)
#guard zpolyAdversarial.toArray.toList = [0, 5, 0, -7]
#guard zpolyTypical.coeff 2 = -2
#guard zpolyEdge.coeff 4 = 0
#guard zpolyAdversarial.coeff 6 = 0

#guard congrOn congrTypicalLeft congrTypicalRight 5 5
#guard congrOn congrEdgeLeft congrEdgeRight 1 5
#guard congrOn congrAdversarialLeft congrAdversarialRight 12 6

example : congr zpolyTypical zpolyTypical 5 := congr_refl zpolyTypical 5
example : congr zpolyEdge zpolyEdge 1 := congr_refl zpolyEdge 1
example : congr zpolyAdversarial zpolyAdversarial 12 := congr_refl zpolyAdversarial 12

#guard bezoutCongrOn coprimeTypicalS coprimeTypicalT coprimeTypicalF coprimeTypicalG 5 5
#guard bezoutCongrOn coprimeEdgeS coprimeEdgeT coprimeEdgeF coprimeEdgeG 7 4
#guard bezoutCongrOn
  coprimeAdversarialS coprimeAdversarialT coprimeAdversarialF coprimeAdversarialG 3 5

example : coprimeModP coprimeEdgeF coprimeEdgeG 7 :=
  coprimeModP_of_bezout coprimeEdgeF coprimeEdgeG coprimeEdgeS coprimeEdgeT 7
    (by
      have h : coprimeEdgeS * coprimeEdgeF + coprimeEdgeT * coprimeEdgeG = (1 : ZPoly) := by
        decide
      simpa [h] using congr_refl (1 : ZPoly) 7)

#guard content contentZero = 0
#guard content contentPrimitive = 1
#guard content contentNontrivial = 6
#guard content contentAdversarial = 7

#guard primitivePart contentZero = (0 : ZPoly)
#guard primitivePart contentPrimitive = contentPrimitive
#guard primitivePart contentNontrivial = contentNontrivialPrimitive
#guard (primitivePart contentAdversarial).toArray.toList = [-2, 3, 0, -1]

#guard DensePoly.scale (content contentZero) (primitivePart contentZero) = contentZero
#guard DensePoly.scale (content contentPrimitive) (primitivePart contentPrimitive) =
  contentPrimitive
#guard DensePoly.scale (content contentNontrivial) (primitivePart contentNontrivial) =
  contentNontrivial
#guard DensePoly.scale (content contentAdversarial) (primitivePart contentAdversarial) =
  contentAdversarial

#guard content (primitivePart contentPrimitive) = 1
#guard content (primitivePart contentNontrivial) = 1
#guard content (primitivePart contentAdversarial) = 1

#guard ratPolyPrimitivePart (DensePoly.ofCoeffs (#[(1 : Rat) / 2, (-1 : Rat) / 2])) =
  DensePoly.ofCoeffs #[-1, 1]
#guard (primitiveSquareFreeDecomposition squareFreeRepeated).primitive =
  squareFreeRepeated
#guard (primitiveSquareFreeDecomposition squareFreeRepeated).squareFreeCore =
  DensePoly.ofCoeffs #[-1, 1]
#guard (primitiveSquareFreeDecomposition squareFreeRepeated).repeatedPart =
  DensePoly.ofCoeffs #[-1, 1]
#guard (primitiveSquareFreeDecomposition squareFreeWithContent).primitive =
  squareFreeRepeated
#guard (primitiveSquareFreeDecomposition squareFreeWithContent).squareFreeCore =
  DensePoly.ofCoeffs #[-1, 1]
#guard (primitiveSquareFreeDecomposition squareFreePowerOfX).squareFreeCore =
  DensePoly.ofCoeffs #[0, 1]
#guard (primitiveSquareFreeDecomposition squareFreeAlreadyCore).squareFreeCore =
  squareFreeAlreadyCore
#guard (primitiveSquareFreeDecomposition squareFreeNegativeConstant).squareFreeCore =
  (1 : ZPoly)
#guard squareFreeCore squareFreeRepeated = DensePoly.ofCoeffs #[-1, 1]

example : Primitive (primitivePart contentPrimitive) := by
  change content (primitivePart contentPrimitive) = 1
  decide

#guard binom 5 2 = 10
#guard binom 6 0 = 1
#guard binom 4 7 = 0

#guard floorSqrt 20 = 4
#guard floorSqrt 0 = 0
#guard floorSqrt 65535 = 255

#guard ceilSqrt 20 = 5
#guard ceilSqrt 0 = 0
#guard ceilSqrt 65535 = 256

#guard coeffNormSq (DensePoly.ofCoeffs #[3, 4]) = 25
#guard coeffNormSq (0 : ZPoly) = 0
#guard coeffNormSq (DensePoly.ofCoeffs #[-6, 0, 8]) = 100

#guard coeffL2NormBound (DensePoly.ofCoeffs #[3, 4]) = 5
#guard coeffL2NormBound (0 : ZPoly) = 0
#guard coeffL2NormBound (DensePoly.ofCoeffs #[-6, 0, 8]) = 10

#guard mignotteCoeffBound (DensePoly.ofCoeffs #[3, 4]) 4 2 = 30
#guard mignotteCoeffBound (0 : ZPoly) 6 3 = 0
#guard mignotteCoeffBound (DensePoly.ofCoeffs #[-6, 0, 8]) 6 3 = 200
#guard mignotteCoeffBound (DensePoly.ofCoeffs #[-6, 0, 8]) 6 3 =
  binom 6 3 * coeffL2NormBound (DensePoly.ofCoeffs #[-6, 0, 8])

end ZPoly

end Hex
