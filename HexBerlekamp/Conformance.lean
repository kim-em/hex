import HexBerlekamp.DistinctDegree

/-!
Core conformance checks for the `HexBerlekamp` Berlekamp, Rabin
irreducibility, certificate-checker, split-step, and distinct-degree surface.

Oracle: FLINT or Sage for external factorisation profiles; core uses Lean-only
property checks.
Mode: if_available
Covered operations:
- `basisSize`, `coeffVector`, `berlekampColumn`, `berlekampMatrix`, and
  `fixedSpaceMatrix`
- `properDivisors`, `maximalProperDivisors`, `frobeniusDiffMod`,
  `rabinDividesTest`, `rabinCoprimeTest`, `rabinWitnesses`, and `rabinTest`
- `checkPowChain`, `checkRabinBezoutWitness`,
  `checkRabinBezoutWitnesses`, and `checkIrreducibilityCertificate`
- `splitFactorAt` and `kernelWitnessSplit?`
- `distinctDegreeCandidate`, `distinctDegreeStep`, and `distinctDegreeFactor`
Covered properties:
- Berlekamp fixed-space matrices subtract the identity from the Frobenius matrix
- Rabin witnesses agree with the per-divisor coprimality checks
- accepted irreducibility certificates have matching pow chains and Bezout
  witnesses, while malformed certificates are rejected
- successful split witnesses multiply back to the split input
- distinct-degree factorization products reconstruct the committed input
Covered edge cases:
- constant, linear, irreducible quadratic, and reducible quadratic inputs over
  `F_5`
- composite degree divisor lists and prime degree divisor lists
- missing pow-chain and wrong-prime certificate data
- split searches with no nontrivial factor, a linear edge input, and a
  reducible quadratic adversarial input
- distinct-degree runs with a unit residual and mixed linear/quadratic factors
-/

namespace Hex
namespace BerlekampConformance

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def vectorNats {n : Nat} (v : Vector (ZMod64 5) n) : List Nat :=
  v.toArray.toList.map ZMod64.toNat

private def matrixNats {n m : Nat} (M : Matrix (ZMod64 5) n m) : List (List Nat) :=
  M.toArray.toList.map vectorNats

private def splitSummary (result : Option (Berlekamp.SplitResult 5)) :
    Option (Nat × List Nat × List Nat) :=
  result.map fun split =>
    (split.splitConstant.toNat, coeffNats split.factor, coeffNats split.cofactor)

private def bucketSummary (buckets : List (Berlekamp.DegreeBucket 5)) :
    List (Nat × List Nat) :=
  buckets.map fun bucket => (bucket.degree, coeffNats bucket.factor)

private def ddfSummary (result : Berlekamp.DistinctDegreeFactorization 5) :
    List (Nat × List Nat) × List Nat :=
  (bucketSummary result.buckets, coeffNats result.residual)

private def unitPoly : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5)]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem unitPoly_monic : DensePoly.Monic unitPoly := by
  rfl

private def linearPoly : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5), 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem linearPoly_monic : DensePoly.Monic linearPoly := by
  rfl

private def irreducibleQuad : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem irreducibleQuad_monic : DensePoly.Monic irreducibleQuad := by
  rfl

private def reducibleQuad : FpPoly 5 :=
  { coeffs := #[(4 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem reducibleQuad_monic : DensePoly.Monic reducibleQuad := by
  rfl

private def mixedDegreePoly : FpPoly 5 :=
  irreducibleQuad * linearPoly

private theorem mixedDegreePoly_monic : DensePoly.Monic mixedDegreePoly := by
  rfl

#guard Berlekamp.basisSize irreducibleQuad = 2
#guard Berlekamp.basisSize linearPoly = 1
#guard Berlekamp.basisSize (0 : FpPoly 5) = 0

#guard vectorNats (Berlekamp.coeffVector irreducibleQuad (polyFive #[4, 3, 1])) = [4, 3]
#guard vectorNats (Berlekamp.coeffVector linearPoly (polyFive #[2, 1])) = [2]
#guard vectorNats (Berlekamp.coeffVector unitPoly (polyFive #[2, 0, 3])) = []

#guard vectorNats
    (Berlekamp.berlekampColumn irreducibleQuad irreducibleQuad_monic ⟨0, by decide⟩) =
  [1, 0]
#guard vectorNats
    (Berlekamp.berlekampColumn irreducibleQuad irreducibleQuad_monic ⟨1, by decide⟩) =
  [0, 4]
#guard vectorNats
    (Berlekamp.berlekampColumn linearPoly linearPoly_monic ⟨0, by decide⟩) =
  [1]

#guard matrixNats (Berlekamp.berlekampMatrix irreducibleQuad irreducibleQuad_monic) =
  [[1, 0], [0, 4]]
#guard matrixNats (Berlekamp.fixedSpaceMatrix irreducibleQuad irreducibleQuad_monic) =
  [[0, 0], [0, 3]]
#guard
  let Q := Berlekamp.berlekampMatrix reducibleQuad reducibleQuad_monic
  let F := Berlekamp.fixedSpaceMatrix reducibleQuad reducibleQuad_monic
  (List.finRange (Berlekamp.basisSize reducibleQuad)).all fun i =>
    (List.finRange (Berlekamp.basisSize reducibleQuad)).all fun j =>
      F[i][j] == Q[i][j] - if i = j then 1 else 0

#guard Berlekamp.properDivisors 6 = [1, 2, 3]
#guard Berlekamp.maximalProperDivisors 6 = [2, 3]
#guard Berlekamp.maximalProperDivisors 5 = [1]

#guard coeffNats (Berlekamp.frobeniusDiffMod irreducibleQuad irreducibleQuad_monic 0) = []
#guard coeffNats (Berlekamp.frobeniusDiffMod irreducibleQuad irreducibleQuad_monic 1) = [0, 3]
#guard coeffNats (Berlekamp.frobeniusDiffMod reducibleQuad reducibleQuad_monic 1) = []

#guard Berlekamp.rabinDividesTest irreducibleQuad irreducibleQuad_monic
#guard Berlekamp.rabinDividesTest linearPoly linearPoly_monic
#guard Berlekamp.rabinDividesTest reducibleQuad reducibleQuad_monic

#guard Berlekamp.rabinCoprimeTest irreducibleQuad irreducibleQuad_monic 1
#guard !Berlekamp.rabinCoprimeTest reducibleQuad reducibleQuad_monic 1
#guard Berlekamp.rabinWitnesses irreducibleQuad irreducibleQuad_monic = [(1, true)]
#guard Berlekamp.rabinWitnesses reducibleQuad reducibleQuad_monic = [(1, false)]
#guard
  (Berlekamp.rabinWitnesses irreducibleQuad irreducibleQuad_monic).all Prod.snd =
    (Berlekamp.maximalProperDivisors (Berlekamp.basisSize irreducibleQuad)).all
      (Berlekamp.rabinCoprimeTest irreducibleQuad irreducibleQuad_monic)

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

private def samePrimeValidCert : Berlekamp.SamePrimeIrreducibilityCertificate 5 where
  n := 2
  powChain := #[polyFive #[0, 1], polyFive #[0, 4], polyFive #[0, 1]]
  bezout :=
    #[{ left := polyFive #[3],
        right := polyFive #[0, 4] }]

#guard Berlekamp.checkPowChain irreducibleQuad irreducibleQuad_monic samePrimeValidCert
#guard
  Berlekamp.checkRabinBezoutWitness irreducibleQuad irreducibleQuad_monic
    samePrimeValidCert 0 1
#guard
  Berlekamp.checkRabinBezoutWitnesses irreducibleQuad irreducibleQuad_monic
    samePrimeValidCert
#guard Berlekamp.checkIrreducibilityCertificate irreducibleQuad irreducibleQuad_monic validQuadCert
#guard !Berlekamp.checkIrreducibilityCertificate irreducibleQuad irreducibleQuad_monic shortPowCert
#guard !Berlekamp.checkIrreducibilityCertificate irreducibleQuad irreducibleQuad_monic wrongPrimeCert

#guard coeffNats (Berlekamp.splitFactorAt reducibleQuad FpPoly.X (ZMod64.ofNat 5 1)) =
  [4, 1]
#guard coeffNats (Berlekamp.splitFactorAt linearPoly FpPoly.X (ZMod64.ofNat 5 1)) =
  [2]
#guard coeffNats (Berlekamp.splitFactorAt irreducibleQuad FpPoly.X (ZMod64.ofNat 5 1)) =
  [3]

#guard splitSummary (Berlekamp.kernelWitnessSplit? reducibleQuad FpPoly.X) =
  some (1, [4, 1], [1, 1])
#guard splitSummary (Berlekamp.kernelWitnessSplit? linearPoly FpPoly.X) = none
#guard splitSummary (Berlekamp.kernelWitnessSplit? irreducibleQuad FpPoly.X) = none
#guard
  match Berlekamp.kernelWitnessSplit? reducibleQuad FpPoly.X with
  | some split => split.factor * split.cofactor == reducibleQuad
  | none => false

#guard coeffNats
    (Berlekamp.distinctDegreeCandidate mixedDegreePoly mixedDegreePoly_monic
      mixedDegreePoly 1) =
  [1, 1]
#guard
  let step := Berlekamp.distinctDegreeStep mixedDegreePoly mixedDegreePoly_monic
    mixedDegreePoly 1
  (step.1.map fun bucket => (bucket.degree, coeffNats bucket.factor), coeffNats step.2) =
    (some (1, [1, 1]), [2, 0, 1])
#guard ddfSummary (Berlekamp.distinctDegreeFactor mixedDegreePoly mixedDegreePoly_monic) =
  ([(1, [1, 1]), (2, [2, 0, 1])], [1])
#guard ddfSummary (Berlekamp.distinctDegreeFactor irreducibleQuad irreducibleQuad_monic) =
  ([(2, [2, 0, 1])], [1])
#guard ddfSummary (Berlekamp.distinctDegreeFactor unitPoly unitPoly_monic) =
  ([], [1])
#guard
  let result := Berlekamp.distinctDegreeFactor mixedDegreePoly mixedDegreePoly_monic
  result.product == mixedDegreePoly

end BerlekampConformance
end Hex
