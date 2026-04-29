import HexPoly.Euclid

/-!
Core conformance checks for `hex-poly`'s dense/basic and Euclidean-operation surface.

Oracle: none
Mode: always
Covered operations:
- dense representation constructors and accessors (`ofCoeffs`, `ofList`, `C`, `monomial`, `size`, `isZero`, `coeff`, `degree?`, `support`, `toArray`)
- basic executable arithmetic (`scale`, `shift`, `add`, `sub`, `mul`, `eval`, `compose`, `derivative`)
- Euclidean helpers (`leadingCoeff`, `divModMonic`, `divMod`, `/`, `%`, `modByMonic`, `gcd`, `xgcd`)
- integer content helpers (`content`, `primitivePart`)
- polynomial CRT witness construction (`polyCRT`)
Covered properties:
- normalization removes trailing zeros from committed raw coefficient inputs
- dense structural equality matches additive identity and commutativity checks on committed fixtures
- scaling by zero and shifting zero collapse back to the normalized zero polynomial
- multiplication by the constant polynomial `1` preserves committed inputs
- Horner evaluation, polynomial composition, and formal derivative agree with committed
  small polynomial calculations
- division fixtures satisfy `quotient * divisor + remainder = dividend`, including exact,
  zero-dividend, and fractional-quotient cases
- `gcd` and `xgcd` agree on committed fixtures and the returned Bezout coefficients
  reconstruct the gcd
- `content` times `primitivePart` reconstructs committed integer polynomials
- `polyCRT` witnesses reduce to both prescribed residues modulo committed coprime monic factors
Covered edge cases:
- the zero polynomial encoded with all-zero trailing coefficients
- sparse polynomials with internal zeros but nonzero leading terms
- shifted and scaled monomials that exercise normalization after arithmetic
- evaluation, composition, and differentiation of zero, constant, and sparse inputs
- Euclidean division with zero dividend, exact division, and non-monic divisors with
  fractional quotients
- integer content for zero, already primitive, and nontrivial-content polynomials
- CRT residues for degree-zero inputs modulo distinct linear monic factors
-/

namespace Hex

namespace DensePoly

private def coeffsTypical : Array Int := #[3, 0, -2, 0, 0]
private def coeffsEdge : Array Int := #[0, 0, 0]
private def coeffsAdversarial : Array Int := #[0, 4, 0, -5, 0, 0]

private def polyTypical : DensePoly Int := ofCoeffs coeffsTypical
private def polyEdge : DensePoly Int := ofCoeffs coeffsEdge
private def polyAdversarial : DensePoly Int := ofCoeffs coeffsAdversarial

private def listTypical : List Int := [-1, 5, 2, 0]
private def listEdge : List Int := [0, 0]
private def listAdversarial : List Int := [0, 7, 0, -3, 0, 0]

private def polyFromListTypical : DensePoly Int := ofList listTypical
private def polyFromListEdge : DensePoly Int := ofList listEdge
private def polyFromListAdversarial : DensePoly Int := ofList listAdversarial

private def constTypical : DensePoly Int := C 5
private def constEdge : DensePoly Int := C 0
private def constAdversarial : DensePoly Int := C (-9)

private def monomialTypical : DensePoly Int := monomial 2 3
private def monomialEdge : DensePoly Int := monomial 4 0
private def monomialAdversarial : DensePoly Int := monomial 3 (-2)

private def ratDivTypicalDividend : DensePoly Rat := ofCoeffs #[1, -2, 0, 1]
private def ratDivTypicalDivisor : DensePoly Rat := ofCoeffs #[-1, 1]
private def ratDivTypicalQuotient : DensePoly Rat := ofCoeffs #[-1, 1, 1]
private def ratDivTypicalRemainder : DensePoly Rat := 0

private def ratDivEdgeDividend : DensePoly Rat := 0
private def ratDivEdgeDivisor : DensePoly Rat := ofCoeffs #[1, 1]
private def ratDivEdgeQuotient : DensePoly Rat := 0
private def ratDivEdgeRemainder : DensePoly Rat := 0

private def ratDivAdversarialDividend : DensePoly Rat := ofCoeffs #[5, -3, 1, 2]
private def ratDivAdversarialDivisor : DensePoly Rat := ofCoeffs #[1, 2]
private def ratDivAdversarialQuotient : DensePoly Rat := ofCoeffs #[-3 / 2, 0, 1]
private def ratDivAdversarialRemainder : DensePoly Rat := ofCoeffs #[13 / 2]

private def ratGcdTypicalLeft : DensePoly Rat := ofCoeffs #[-2, 1, 1]
private def ratGcdTypicalRight : DensePoly Rat := ofCoeffs #[-3, 2, 1]
private def ratGcdTypicalValue : DensePoly Rat := ofCoeffs #[1, -1]

private def ratGcdEdgeLeft : DensePoly Rat := 0
private def ratGcdEdgeRight : DensePoly Rat := ofCoeffs #[2, 1]

private def ratGcdAdversarialLeft : DensePoly Rat := ofCoeffs #[2, 5, 2]
private def ratGcdAdversarialRight : DensePoly Rat := ofCoeffs #[1, 2]

private def intContentZero : DensePoly Int := ofCoeffs #[0, 0, 0]
private def intContentPrimitive : DensePoly Int := ofCoeffs #[-1, 0, 2]
private def intContentNontrivial : DensePoly Int := ofCoeffs #[-6, 0, 12]

private def crtModA : DensePoly Rat := ofCoeffs #[0, 1]
private def crtModB : DensePoly Rat := ofCoeffs #[-1, 1]
private def crtResidueA : DensePoly Rat := C 5
private def crtResidueB : DensePoly Rat := C 7
private def crtBezoutS : DensePoly Rat := C 1
private def crtBezoutT : DensePoly Rat := C (-1)
private def crtWitness : DensePoly Rat :=
  polyCRT crtModA crtModB crtResidueA crtResidueB crtBezoutS crtBezoutT

-- `#eval` refuses to reduce `DensePoly` values because `ofCoeffs` and `monomial`
-- still carry sorry-backed normalization proofs in their propositional fields.
/-- info: [3, 0, -2] -/
#guard_msgs in #eval! polyTypical.toArray.toList

/-- info: [] -/
#guard_msgs in #eval! polyEdge.toArray.toList

/-- info: [0, 4, 0, -5] -/
#guard_msgs in #eval! polyAdversarial.toArray.toList

#guard polyTypical = ofCoeffs #[3, 0, -2]
#guard polyEdge = (0 : DensePoly Int)
#guard polyAdversarial.support = [1, 3]

#guard polyFromListTypical.toArray.toList = [-1, 5, 2]
#guard polyFromListEdge = (0 : DensePoly Int)
#guard polyFromListAdversarial.toArray.toList = [0, 7, 0, -3]

#guard constTypical.toArray.toList = [5]
#guard constEdge = (0 : DensePoly Int)
#guard constAdversarial.toArray.toList = [-9]

#guard monomialTypical.toArray.toList = [0, 0, 3]
#guard monomialEdge = (0 : DensePoly Int)
#guard monomialAdversarial.toArray.toList = [0, 0, 0, -2]

#guard polyTypical.size = 3
#guard polyEdge.size = 0
#guard polyAdversarial.size = 4

#guard !polyTypical.isZero
#guard polyEdge.isZero
#guard !monomialAdversarial.isZero

#guard polyTypical.coeff 2 = -2
#guard polyEdge.coeff 0 = 0
#guard polyAdversarial.coeff 5 = 0

#guard polyTypical.degree? = some 2
#guard polyEdge.degree? = none
#guard monomialAdversarial.degree? = some 3

#guard polyTypical.support = [0, 2]
#guard polyEdge.support = []
#guard polyAdversarial.support = [1, 3]

#guard polyTypical.toArray.toList = [3, 0, -2]
#guard polyEdge.toArray.toList = []
#guard monomialAdversarial.toArray.toList = [0, 0, 0, -2]

/-- info: [9, 0, -6] -/
#guard_msgs in #eval! (scale 3 polyTypical).toArray.toList

#guard scale 0 polyAdversarial = (0 : DensePoly Int)
#guard (scale (-2) monomialAdversarial).toArray.toList = [0, 0, 0, 4]

/-- info: [0, 0, 3, 0, -2] -/
#guard_msgs in #eval! (shift 2 polyTypical).toArray.toList

#guard shift 0 polyEdge = (0 : DensePoly Int)
#guard (shift 1 monomialAdversarial).toArray.toList = [0, 0, 0, 0, -2]

/-- info: [2, 5] -/
#guard_msgs in #eval! (polyTypical + polyFromListTypical).toArray.toList

#guard polyEdge + constEdge = (0 : DensePoly Int)
#guard (polyAdversarial + monomialAdversarial).toArray.toList = [0, 4, 0, -7]
#guard polyTypical + (0 : DensePoly Int) = polyTypical
#guard polyTypical + polyFromListTypical = polyFromListTypical + polyTypical

/-- info: [4, -5, -4] -/
#guard_msgs in #eval! (polyTypical - polyFromListTypical).toArray.toList

#guard polyEdge - constEdge = (0 : DensePoly Int)
#guard (polyAdversarial - monomialAdversarial).toArray.toList = [0, 4, 0, -3]

/-- info: [-3, 15, 8, -10, -4] -/
#guard_msgs in #eval! (polyTypical * polyFromListTypical).toArray.toList

#guard polyEdge * constEdge = (0 : DensePoly Int)
#guard (polyAdversarial * monomialAdversarial).toArray.toList = [0, 0, 0, 0, -8, 0, 10]
#guard polyTypical * C 1 = polyTypical

#guard eval polyTypical 2 = -5
#guard eval polyEdge 7 = 0
#guard eval polyAdversarial (-1) = 1

/-- info: [-5] -/
#guard_msgs in #eval! (compose polyTypical (C 2)).toArray.toList

#guard compose polyEdge polyTypical = (0 : DensePoly Int)
#guard (compose polyAdversarial (monomial 1 (-1))).toArray.toList = [0, -4, 0, 5]

/-- info: [0, -4] -/
#guard_msgs in #eval! (derivative polyTypical).toArray.toList

#guard derivative polyEdge = (0 : DensePoly Int)
#guard (derivative polyAdversarial).toArray.toList = [4, 0, -15]

#guard ratDivTypicalDividend.leadingCoeff = 1
#guard ratDivEdgeDividend.leadingCoeff = 0
#guard ratDivAdversarialDividend.leadingCoeff = 2

#guard divModMonic ratDivTypicalDividend ratDivTypicalDivisor (by rfl) =
  (ratDivTypicalQuotient, ratDivTypicalRemainder)
#guard divModMonic ratDivEdgeDividend ratDivEdgeDivisor (by rfl) =
  (ratDivEdgeQuotient, ratDivEdgeRemainder)
#guard divModMonic ratGcdTypicalLeft ratDivTypicalDivisor (by rfl) =
  (ofCoeffs #[2, 1], 0)

#guard divMod ratDivTypicalDividend ratDivTypicalDivisor =
  (ratDivTypicalQuotient, ratDivTypicalRemainder)
#guard divMod ratDivEdgeDividend ratDivEdgeDivisor =
  (ratDivEdgeQuotient, ratDivEdgeRemainder)
#guard divMod ratDivAdversarialDividend ratDivAdversarialDivisor =
  (ratDivAdversarialQuotient, ratDivAdversarialRemainder)

#guard ratDivTypicalDividend / ratDivTypicalDivisor = ratDivTypicalQuotient
#guard ratDivEdgeDividend / ratDivEdgeDivisor = ratDivEdgeQuotient
#guard ratDivAdversarialDividend / ratDivAdversarialDivisor = ratDivAdversarialQuotient

#guard ratDivTypicalDividend % ratDivTypicalDivisor = ratDivTypicalRemainder
#guard ratDivEdgeDividend % ratDivEdgeDivisor = ratDivEdgeRemainder
#guard ratDivAdversarialDividend % ratDivAdversarialDivisor = ratDivAdversarialRemainder

#guard modByMonic ratDivTypicalDividend ratDivTypicalDivisor (by rfl) =
  ratDivTypicalRemainder
#guard modByMonic ratDivEdgeDividend ratDivEdgeDivisor (by rfl) =
  ratDivEdgeRemainder
#guard modByMonic ratGcdTypicalLeft ratDivTypicalDivisor (by rfl) = 0

#guard ratDivTypicalQuotient * ratDivTypicalDivisor + ratDivTypicalRemainder =
  ratDivTypicalDividend
#guard ratDivEdgeQuotient * ratDivEdgeDivisor + ratDivEdgeRemainder =
  ratDivEdgeDividend
#guard ratDivAdversarialQuotient * ratDivAdversarialDivisor + ratDivAdversarialRemainder =
  ratDivAdversarialDividend

#guard gcd ratGcdTypicalLeft ratGcdTypicalRight = ratGcdTypicalValue
#guard gcd ratGcdEdgeLeft ratGcdEdgeRight = ratGcdEdgeRight
#guard gcd ratGcdAdversarialLeft ratGcdAdversarialRight = ratGcdAdversarialRight

#guard (xgcd ratGcdTypicalLeft ratGcdTypicalRight).gcd = ratGcdTypicalValue
#guard (xgcd ratGcdEdgeLeft ratGcdEdgeRight).gcd = ratGcdEdgeRight
#guard (xgcd ratGcdAdversarialLeft ratGcdAdversarialRight).gcd = ratGcdAdversarialRight

#guard
  let r := xgcd ratGcdTypicalLeft ratGcdTypicalRight
  r.left * ratGcdTypicalLeft + r.right * ratGcdTypicalRight = r.gcd
#guard
  let r := xgcd ratGcdEdgeLeft ratGcdEdgeRight
  r.left * ratGcdEdgeLeft + r.right * ratGcdEdgeRight = r.gcd
#guard
  let r := xgcd ratGcdAdversarialLeft ratGcdAdversarialRight
  r.left * ratGcdAdversarialLeft + r.right * ratGcdAdversarialRight = r.gcd

#guard content intContentZero = 0
#guard content intContentPrimitive = 1
#guard content intContentNontrivial = 6

#guard primitivePart intContentZero = 0
#guard primitivePart intContentPrimitive = intContentPrimitive
#guard primitivePart intContentNontrivial = intContentPrimitive

#guard scale (content intContentZero) (primitivePart intContentZero) = intContentZero
#guard scale (content intContentPrimitive) (primitivePart intContentPrimitive) =
  intContentPrimitive
#guard scale (content intContentNontrivial) (primitivePart intContentNontrivial) =
  intContentNontrivial

#guard crtBezoutS * crtModA + crtBezoutT * crtModB = 1
#guard crtWitness = ofCoeffs #[5, 2]
#guard crtWitness % crtModA = crtResidueA % crtModA
#guard crtWitness % crtModB = crtResidueB % crtModB

end DensePoly

end Hex
