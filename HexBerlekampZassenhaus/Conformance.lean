import HexBerlekampZassenhaus.Basic

/-!
Core conformance checks for the executable `HexBerlekampZassenhaus` surface.

Oracle: FLINT or Sage for external integer-factorisation profiles; core uses
Lean-only property checks.
Mode: always
Covered operations:
- `ZPoly.extractXPower`, `normalizeForFactor`, `normalizationPrefixFactors`,
  and `reassembleNormalizedFactors`
- `isGoodPrime`, `choosePrime`, and `choosePrimeData`
- `recombinationSearch` and `recombine`
- `factorWithBound` and `factor`
- `PrimeFactorData.checkFactorCerts`, `PrimeFactorData.checkForPolynomial`,
  `DegreeObstruction.checkForCertificate`, and `checkIrreducibleCert`
Covered properties:
- normalization exposes content, powers of `X`, square-free cores, and factor
  prefixes whose ordered products reconstruct committed inputs
- good-prime selection rejects bad leading-coefficient and nonsquare-free
  cases while selected data agrees with the chosen prime
- successful recombination and public factor entry points multiply back to the
  committed input, while malformed lifted data fails explicitly
- integer irreducibility certificates validate the concrete modular factor
  product, nested Rabin certificates, and degree-obstruction data
Covered edge cases:
- zero, constant, linear, repeated-root, and initial-zero polynomial inputs
- primes that divide a leading coefficient and primes with repeated modular
  reductions
- empty lifted-factor data, exact linear-factor recombination, and deliberate
  non-divisor recombination data
- LLL recombination on a ten-local-factor input, exhaustive-oracle agreement on
  a small input, and empty/single-factor trivial lattices
- empty, positive, wrong-prime, and malformed nested certificate records
-/

namespace Hex
namespace BerlekampZassenhausConformance

private instance boundsTwo : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
private instance boundsThree : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem one_ne_zero_three : (1 : ZMod64 3) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 3) 1 0).mp h
  simp at hm

private def zpoly (coeffs : Array Int) : ZPoly :=
  DensePoly.ofCoeffs coeffs

private def zcoeffs (f : ZPoly) : List Int :=
  f.toArray.toList

private def fpCoeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def fp3CoeffNats (f : FpPoly 3) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def polyThree (coeffs : Array Nat) : FpPoly 3 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 3 n))

private def normSummary (d : FactorNormalizationData) :
    Int × List Int × Nat × List Int × List Int × List Int :=
  (d.content, zcoeffs d.primitive, d.xPower, zcoeffs d.xFreePrimitive,
    zcoeffs d.squareFreeCore, zcoeffs d.repeatedPart)

private def primeDataSummary (d : PrimeChoiceData) : Nat × Nat × Nat :=
  letI := d.bounds
  (d.p, d.fModP.degree?.getD 0, d.factorsModP.size)

private def factorProductMatches (f : ZPoly) (factors : Array ZPoly) : Bool :=
  Array.polyProduct factors == f

private def certPassesForFactor
    (d : PrimeFactorData) (degree : Nat) (factor : @FpPoly d.p d.bounds)
    (cert : Berlekamp.IrreducibilityCertificate) : Bool :=
  d.checkCertAtFactor degree factor cert

private def normalizationTypical : ZPoly :=
  zpoly #[-2, 0, 2]

private def normalizationEdge : ZPoly :=
  0

private def normalizationAdversarial : ZPoly :=
  zpoly #[0, 0, 2, -4, 2, 0, 0]

#guard
  normSummary (normalizeForFactor normalizationTypical) =
    (2, [-1, 0, 1], 0, [-1, 0, 1], [-1, 0, 1], [1])
#guard
  normSummary (normalizeForFactor normalizationEdge) =
    (0, [], 0, [], [], [])
#guard
  normSummary (normalizeForFactor normalizationAdversarial) =
    (2, [0, 0, 1, -2, 1], 2, [1, -2, 1], [-1, 1], [-1, 1])

#guard
  let d := ZPoly.extractXPower normalizationTypical
  (d.power, zcoeffs d.core) = (0, [-2, 0, 2])
#guard
  let d := ZPoly.extractXPower normalizationEdge
  (d.power, zcoeffs d.core) = (0, [])
#guard
  let d := ZPoly.extractXPower normalizationAdversarial
  (d.power, zcoeffs d.core) = (2, [2, -4, 2])

#guard
  let d := normalizeForFactor normalizationTypical
  factorProductMatches normalizationTypical (normalizationPrefixFactors d ++ #[d.squareFreeCore])
#guard
  let d := normalizeForFactor normalizationEdge
  factorProductMatches normalizationEdge (normalizationPrefixFactors d ++ #[d.squareFreeCore])
#guard
  let d := normalizeForFactor normalizationAdversarial
  factorProductMatches normalizationAdversarial (normalizationPrefixFactors d ++ #[d.squareFreeCore])

#guard
  let d := normalizeForFactor normalizationTypical
  factorProductMatches normalizationTypical (reassembleNormalizedFactors d #[d.squareFreeCore])
#guard
  let d := normalizeForFactor normalizationEdge
  factorProductMatches normalizationEdge (reassembleNormalizedFactors d #[d.squareFreeCore])
#guard
  let d := normalizeForFactor normalizationAdversarial
  factorProductMatches normalizationAdversarial (reassembleNormalizedFactors d #[d.squareFreeCore])

private def primeTypical : ZPoly :=
  zpoly #[1, 0, 1]

private def primeEdgeLinear : ZPoly :=
  zpoly #[1, 1]

private def primeAdversarialLeading : ZPoly :=
  zpoly #[1, 0, 5]

private def primeAdversarialRepeated : ZPoly :=
  zpoly #[1, 2, 1]

#guard isGoodPrime primeTypical 3
#guard isGoodPrime primeEdgeLinear 2
#guard !isGoodPrime primeAdversarialLeading 5
#guard !isGoodPrime primeAdversarialRepeated 2
#guard !isGoodPrime primeAdversarialRepeated 3

#guard choosePrime primeTypical = 3
#guard choosePrime primeEdgeLinear = 2
#guard choosePrime primeAdversarialLeading = 3

#guard
  let d := choosePrimeData primeTypical
  primeDataSummary d = (choosePrime primeTypical, 2, 1)
#guard
  let d := choosePrimeData primeEdgeLinear
  primeDataSummary d = (choosePrime primeEdgeLinear, 1, 1)
#guard
  let d := choosePrimeData primeAdversarialLeading
  d.p = choosePrime primeAdversarialLeading && d.factorsModP.size > 0

private def recombineTypicalTarget : ZPoly :=
  zpoly #[2, 3, 1]

private def recombineTypicalLift : LiftData :=
  { p := 5
    k := 2
    liftedFactors := #[zpoly #[1, 1], zpoly #[2, 1]] }

private def recombineEdgeLift : LiftData :=
  { p := 5
    k := 0
    liftedFactors := #[] }

private def recombineAdversarialLift : LiftData :=
  { p := 5
    k := 2
    liftedFactors := #[zpoly #[3, 1]] }

private def linearFactor (root : Int) : ZPoly :=
  zpoly #[-root, 1]

private def productLinearFactors (roots : List Int) : ZPoly :=
  Array.polyProduct (roots.map linearFactor).toArray

private def recombineLargeTarget : ZPoly :=
  productLinearFactors [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

private def recombineLargeLift : LiftData :=
  { p := 11
    k := 2
    liftedFactors := (List.range 10).map (fun i => linearFactor (Int.ofNat (i + 1))) |>.toArray }

private def recombineLargeFactors : Array ZPoly :=
  factorWithBound recombineLargeTarget 8

private def recombineSingleTarget : ZPoly :=
  zpoly #[3, 1]

private def recombineSingleLift : LiftData :=
  { p := 5
    k := 2
    liftedFactors := #[recombineSingleTarget] }

private def exhaustiveOracle (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match recombinationSearch f d.liftedFactors.toList with
  | some factors => factors.toArray
  | none => #[]

#guard
  (recombinationSearch recombineTypicalTarget recombineTypicalLift.liftedFactors.toList).isSome
#guard recombinationSearch (1 : ZPoly) recombineEdgeLift.liftedFactors.toList = some []
#guard
  recombinationSearch recombineTypicalTarget recombineAdversarialLift.liftedFactors.toList = none

#guard factorProductMatches recombineTypicalTarget (recombine recombineTypicalTarget recombineTypicalLift)
#guard recombine (1 : ZPoly) recombineEdgeLift = #[]
#guard recombine recombineSingleTarget recombineSingleLift = #[recombineSingleTarget]
#guard recombine recombineTypicalTarget recombineAdversarialLift = #[]
#guard recombine recombineTypicalTarget recombineTypicalLift =
  exhaustiveOracle recombineTypicalTarget recombineTypicalLift
#guard recombineLargeLift.liftedFactors.size >= 10
#guard factorProductMatches recombineLargeTarget (recombine recombineLargeTarget recombineLargeLift)
#guard factorProductMatches recombineLargeTarget recombineLargeFactors

private def factorTypical : ZPoly :=
  zpoly #[2, 3, 1]

private def factorEdgeConstant : ZPoly :=
  zpoly #[6]

private def factorAdversarialXPower : ZPoly :=
  zpoly #[0, 0, 1, 1]

#guard factorProductMatches factorTypical (factorWithBound factorTypical 8)
#guard factorProductMatches factorEdgeConstant (factorWithBound factorEdgeConstant 1)
#guard factorProductMatches factorAdversarialXPower (factorWithBound factorAdversarialXPower 8)

#guard factorProductMatches factorTypical (factor factorTypical)
#guard factorProductMatches factorEdgeConstant (factor factorEdgeConstant)
#guard factorProductMatches factorAdversarialXPower (factor factorAdversarialXPower)

private def irreducibleIntegerQuad : ZPoly :=
  zpoly #[2, 0, 1]

private def positiveIntegerQuad : ZPoly :=
  zpoly #[1, 0, 1]

private def irreducibleQuad : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem irreducibleQuad_monic : DensePoly.Monic irreducibleQuad := by
  rfl

private def positiveQuad : FpPoly 3 :=
  { coeffs := #[(1 : ZMod64 3), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_three }

private theorem positiveQuad_monic : DensePoly.Monic positiveQuad := by
  rfl

private def validPositiveQuadCert : Berlekamp.IrreducibilityCertificate where
  p := 3
  n := 2
  powChain := #[polyThree #[0, 1], polyThree #[0, 2], polyThree #[0, 1]]
  bezout :=
    #[{ left := polyThree #[1],
        right := polyThree #[0, 2] }]

private def validQuadCert : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[polyFive #[0, 1], polyFive #[0, 4], polyFive #[0, 1]]
  bezout :=
    #[{ left := polyFive #[3],
        right := polyFive #[0, 4] }]

private def shortPowCert : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[polyFive #[0, 1], polyFive #[0, 4]]
  bezout :=
    #[{ left := polyFive #[3],
        right := polyFive #[0, 4] }]

private def wrongPrimeCert : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(ZMod64.ofNat 7 0), ZMod64.ofNat 7 1]]
  bezout := #[]

private def positivePrimeData : PrimeFactorData where
  p := 3
  factorDegrees := #[2]
  factorPolys := #[positiveQuad]
  factorCerts := #[validPositiveQuadCert]

private def malformedPrimeData : PrimeFactorData where
  p := 5
  factorDegrees := #[2]
  factorPolys := #[irreducibleQuad]
  factorCerts := #[shortPowCert]

private def wrongPrimeNestedData : PrimeFactorData where
  p := 5
  factorDegrees := #[2]
  factorPolys := #[irreducibleQuad]
  factorCerts := #[wrongPrimeCert]

private def positiveObstruction : DegreeObstruction where
  targetDegree := 1
  primeIndex := 0

private def missingPrimeObstruction : DegreeObstruction where
  targetDegree := 1
  primeIndex := 1

private def positiveIntegerCert : ZPolyIrreducibilityCertificate where
  perPrime := #[positivePrimeData]
  degreeObstructions := #[positiveObstruction]

private def malformedIntegerCert : ZPolyIrreducibilityCertificate where
  perPrime := #[malformedPrimeData]
  degreeObstructions := #[positiveObstruction]

private def emptyIntegerCert : ZPolyIrreducibilityCertificate where
  perPrime := #[]
  degreeObstructions := #[]

#guard fp3CoeffNats positivePrimeData.factorProduct = fp3CoeffNats (ZPoly.modP 3 positiveIntegerQuad)
#guard positivePrimeData.factorProduct == ZPoly.modP 3 positiveIntegerQuad
#guard isGoodPrime positiveIntegerQuad 3
#guard positivePrimeData.degreeSum = 2
#guard positivePrimeData.hasSubsetDegree 2
#guard !positivePrimeData.hasSubsetDegree 1

#guard
  certPassesForFactor positivePrimeData 2 positiveQuad validPositiveQuadCert
#guard
  !certPassesForFactor malformedPrimeData 2 irreducibleQuad shortPowCert
#guard
  !certPassesForFactor wrongPrimeNestedData 2 irreducibleQuad wrongPrimeCert

#guard positivePrimeData.checkFactorCerts
#guard !malformedPrimeData.checkFactorCerts
#guard !wrongPrimeNestedData.checkFactorCerts

#guard positivePrimeData.checkForPolynomial positiveIntegerQuad
#guard !malformedPrimeData.checkForPolynomial irreducibleIntegerQuad
#guard !wrongPrimeNestedData.checkForPolynomial irreducibleIntegerQuad

#guard positiveObstruction.checkForCertificate positiveIntegerQuad positiveIntegerCert
#guard !missingPrimeObstruction.checkForCertificate positiveIntegerQuad positiveIntegerCert
#guard !positiveObstruction.checkForCertificate positiveIntegerQuad emptyIntegerCert

#guard checkIrreducibleCert positiveIntegerQuad positiveIntegerCert
#guard !checkIrreducibleCert irreducibleIntegerQuad malformedIntegerCert
#guard !checkIrreducibleCert irreducibleIntegerQuad emptyIntegerCert

end BerlekampZassenhausConformance
end Hex
