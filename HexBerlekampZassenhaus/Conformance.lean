import HexBerlekampZassenhaus

/-!
Lean-only conformance checks for the executable Berlekamp-Zassenhaus surface.

These guards focus on the integer irreducibility certificate checker: each
recorded nested Rabin certificate must be checked against the concrete modular
factor it certifies, not just against matching prime and degree metadata.
-/

namespace Hex

private theorem bounds_five : ZMod64.Bounds 5 := by
  constructor <;> decide

private def zpoly (coeffs : List Int) : ZPoly :=
  DensePoly.ofCoeffs coeffs.toArray

private def polyFive (coeffs : List Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs <| coeffs.map (fun n => (ZMod64.ofNat 5 n : ZMod64 5)) |>.toArray

private def irreducibleIntegerQuad : ZPoly :=
  zpoly [2, 0, 1]

private def irreducibleQuad : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      decide }

private def shortPowCert : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[polyFive [0, 1], polyFive [0, 4]]
  bezout :=
    #[{ left := polyFive [3],
        right := polyFive [0, 4] }]

private def malformedPrimeData : PrimeFactorData where
  p := 5
  factorDegrees := #[2]
  factorPolys := #[irreducibleQuad]
  factorCerts := #[shortPowCert]

private def malformedIntegerCert : ZPolyIrreducibilityCertificate where
  perPrime := #[malformedPrimeData]
  degreeObstructions := #[{ targetDegree := 1, primeIndex := 0 }]

#guard malformedPrimeData.factorDegrees == #[2]
#guard shortPowCert.p == 5
#guard shortPowCert.n == 2
#guard malformedPrimeData.factorPolys[0]?.map (fun factor => factor.degree?) = some (some 2)
#guard !malformedPrimeData.checkFactorCerts
#guard !malformedPrimeData.checkForPolynomial irreducibleIntegerQuad
#guard !checkIrreducibleCert irreducibleIntegerQuad malformedIntegerCert

end Hex
