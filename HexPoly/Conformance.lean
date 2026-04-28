import HexPoly.Operations

/-!
Core conformance checks for `hex-poly`'s first dense/basic-operations slice.

Oracle: none
Mode: always
Covered operations:
- dense representation constructors and accessors (`ofCoeffs`, `ofList`, `C`, `monomial`, `size`, `isZero`, `coeff`, `degree?`, `support`, `toArray`)
- basic executable arithmetic (`scale`, `shift`, `add`, `sub`, `mul`)
Covered properties:
- normalization removes trailing zeros from committed raw coefficient inputs
- dense structural equality matches additive identity and commutativity checks on committed fixtures
- scaling by zero and shifting zero collapse back to the normalized zero polynomial
- multiplication by the constant polynomial `1` preserves committed inputs
Covered edge cases:
- the zero polynomial encoded with all-zero trailing coefficients
- sparse polynomials with internal zeros but nonzero leading terms
- shifted and scaled monomials that exercise normalization after arithmetic
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

end DensePoly

end Hex
