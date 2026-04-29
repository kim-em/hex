import HexGramSchmidt.Update

/-!
Core conformance checks for `HexGramSchmidt`.

Oracle: none.
Mode: always.

Covered operations:
- `Hex.GramSchmidt.Int.gramDet`
- `Hex.GramSchmidt.Int.gramDetVec`
- `Hex.GramSchmidt.Int.scaledCoeffs`
- `Hex.GramSchmidt.Rat.gramDet`
- `Hex.GramSchmidt.Int.sizeReduce`
- `Hex.GramSchmidt.Int.adjacentSwap`
- adjacent-swap exact-update helpers for Gram determinants and scaled
  coefficients

Covered properties:
- `gramDetVec` agrees with `gramDet` on committed integer matrices.
- selected leading Gram determinants match hand-computed values.
- `scaledCoeffs` has Gram-determinant diagonal entries.
- `scaledCoeffs` has zero entries above the diagonal.
- selected lower-triangular scaled coefficients match the determinant
  formula used by the implementation.
- rational Gram determinants match hand-computed leading Gram minors.
- size reduction and adjacent swaps perform the advertised row operations.
- adjacent-swap helper numerators and quotients match the formulas consumed
  by the update theorem surface.

Covered edge cases:
- a nonsingular `3 x 3` basis with nonzero off-diagonal Gram products.
- a zero `2 x 2` basis.
- a dependent `3 x 2` input whose leading prefix becomes singular.
- a rational matrix with fractional entries.
- negative and positive coefficients in lower scaled-coefficient entries.
- above-diagonal entries away from the first row.
- the empty-prefix Gram determinant convention.
- size reduction with positive and negative reduction coefficients.
- adjacent swaps at the first and second nonzero row positions.
-/

namespace Hex
namespace GramSchmidtConformance

private def typical : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 2 => 1
    | 2, 1 => 1
    | 2, 2 => 1
    | _, _ => 0

private def zeroEdge : Matrix Int 2 2 := 0

private def dependent : Matrix Int 3 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 2
    | 1, 0 => 4
    | 2, 0 => -1
    | 2, 1 => 3
    | _, _ => 0

private def typicalRat : Matrix Rat 3 3 :=
  Matrix.ofFn fun i j => (typical[i][j] : Rat)

private def zeroRat : Matrix Rat 2 2 := 0

private def fractionalRat : Matrix Rat 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => (1 : Rat) / 2
    | 1, 1 => 2
    | _, _ => 0

private abbrev f0_3 : Fin 3 := ⟨0, by decide⟩
private abbrev f1_3 : Fin 3 := ⟨1, by decide⟩
private abbrev f2_3 : Fin 3 := ⟨2, by decide⟩
private abbrev f0_2 : Fin 2 := ⟨0, by decide⟩
private abbrev f1_2 : Fin 2 := ⟨1, by decide⟩

private def gramDetVecAgrees {n m : Nat} (b : Matrix Int n m) : Bool :=
  (List.range (n + 1)).all fun k =>
    if hk : k ≤ n then
      (GramSchmidt.Int.gramDetVec b).get ⟨k, Nat.lt_succ_of_le hk⟩ =
        GramSchmidt.Int.gramDet b k hk
    else
      true

#guard gramDetVecAgrees typical
#guard gramDetVecAgrees zeroEdge
#guard gramDetVecAgrees dependent

#guard GramSchmidt.Int.gramDet typical 0 (by decide) = 1
#guard GramSchmidt.Int.gramDet typical 1 (by decide) = 2
#guard GramSchmidt.Int.gramDet typical 2 (by decide) = 3
#guard GramSchmidt.Int.gramDet typical 3 (by decide) = 4

#guard GramSchmidt.Int.gramDet zeroEdge 0 (by decide) = 1
#guard GramSchmidt.Int.gramDet zeroEdge 1 (by decide) = 0
#guard GramSchmidt.Int.gramDet zeroEdge 2 (by decide) = 0

#guard GramSchmidt.Int.gramDet dependent 0 (by decide) = 1
#guard GramSchmidt.Int.gramDet dependent 1 (by decide) = 4
#guard GramSchmidt.Int.gramDet dependent 2 (by decide) = 0
#guard GramSchmidt.Int.gramDet dependent 3 (by decide) = 0

#guard GramSchmidt.Rat.gramDet typicalRat 0 (by decide) = 1
#guard GramSchmidt.Rat.gramDet typicalRat 1 (by decide) = 2
#guard GramSchmidt.Rat.gramDet typicalRat 2 (by decide) = 3
#guard GramSchmidt.Rat.gramDet typicalRat 3 (by decide) = 4

#guard GramSchmidt.Rat.gramDet zeroRat 0 (by decide) = 1
#guard GramSchmidt.Rat.gramDet zeroRat 1 (by decide) = 0
#guard GramSchmidt.Rat.gramDet zeroRat 2 (by decide) = 0

#guard GramSchmidt.Rat.gramDet fractionalRat 0 (by decide) = 1
#guard GramSchmidt.Rat.gramDet fractionalRat 1 (by decide) = (1 : Rat) / 4
#guard GramSchmidt.Rat.gramDet fractionalRat 2 (by decide) = 1

#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f0_3 f0_3 = 2
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f1_3 f1_3 = 3
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f2_3 f2_3 = 4
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f1_3 f0_3 = 1
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f2_3 f0_3 = 1
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f2_3 f1_3 = 1
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f0_3 f1_3 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f0_3 f2_3 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs typical) f1_3 f2_3 = 0

#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs zeroEdge) f0_2 f0_2 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs zeroEdge) f1_2 f1_2 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs zeroEdge) f1_2 f0_2 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs zeroEdge) f0_2 f1_2 = 0

#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs dependent) f0_3 f0_3 = 4
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs dependent) f1_3 f1_3 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs dependent) f2_3 f2_3 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs dependent) f1_3 f0_3 = 8
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs dependent) f2_3 f0_3 = -2
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs dependent) f2_3 f1_3 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs dependent) f0_3 f1_3 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.scaledCoeffs dependent) f1_3 f2_3 = 0

#guard GramSchmidt.entry (GramSchmidt.Int.sizeReduce typical f0_3 f2_3 2) f2_3 f0_3 = -2
#guard GramSchmidt.entry (GramSchmidt.Int.sizeReduce typical f0_3 f2_3 2) f2_3 f1_3 = -1
#guard GramSchmidt.entry (GramSchmidt.Int.sizeReduce typical f0_3 f2_3 2) f2_3 f2_3 = 1

#guard GramSchmidt.entry (GramSchmidt.Int.sizeReduce zeroEdge f0_2 f1_2 7) f1_2 f0_2 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.sizeReduce zeroEdge f0_2 f1_2 7) f1_2 f1_2 = 0

#guard GramSchmidt.entry (GramSchmidt.Int.sizeReduce dependent f0_3 f2_3 (-1)) f2_3 f0_2 = 1
#guard GramSchmidt.entry (GramSchmidt.Int.sizeReduce dependent f0_3 f2_3 (-1)) f2_3 f1_2 = 3

#guard GramSchmidt.entry (GramSchmidt.Int.adjacentSwap typical f1_3 (by decide)) f0_3 f0_3 = 1
#guard GramSchmidt.entry (GramSchmidt.Int.adjacentSwap typical f1_3 (by decide)) f0_3 f1_3 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.adjacentSwap typical f1_3 (by decide)) f1_3 f1_3 = 1

#guard GramSchmidt.entry (GramSchmidt.Int.adjacentSwap zeroEdge f1_2 (by decide)) f0_2 f0_2 = 0
#guard GramSchmidt.entry (GramSchmidt.Int.adjacentSwap zeroEdge f1_2 (by decide)) f1_2 f1_2 = 0

#guard GramSchmidt.entry (GramSchmidt.Int.adjacentSwap dependent f2_3 (by decide)) f1_3 f0_2 = -1
#guard GramSchmidt.entry (GramSchmidt.Int.adjacentSwap dependent f2_3 (by decide)) f1_3 f1_2 = 3
#guard GramSchmidt.entry (GramSchmidt.Int.adjacentSwap dependent f2_3 (by decide)) f2_3 f0_2 = 4

#guard GramSchmidt.Int.adjacentSwapDenom typical f1_3 = 2
#guard GramSchmidt.Int.adjacentSwapPivotCoeff typical f1_3 (by decide) = 1
#guard GramSchmidt.Int.adjacentSwapGramDetNumerator typical f1_3 (by decide) = 4
#guard GramSchmidt.Int.adjacentSwapGramDetQuotient typical f1_3 (by decide) = 2
#guard GramSchmidt.Int.adjacentSwapScaledCoeffAbovePrevNumerator typical f1_3 (by decide) f2_3 = 3
#guard GramSchmidt.Int.adjacentSwapScaledCoeffAboveCurrNumerator typical f1_3 (by decide) f2_3 = 0

#guard GramSchmidt.Int.adjacentSwapDenom typical f2_3 = 3
#guard GramSchmidt.Int.adjacentSwapPivotCoeff typical f2_3 (by decide) = 1
#guard GramSchmidt.Int.adjacentSwapGramDetNumerator typical f2_3 (by decide) = 9
#guard GramSchmidt.Int.adjacentSwapGramDetQuotient typical f2_3 (by decide) = 3

#guard GramSchmidt.Int.adjacentSwapDenom dependent f1_3 = 4
#guard GramSchmidt.Int.adjacentSwapPivotCoeff dependent f1_3 (by decide) = 8
#guard GramSchmidt.Int.adjacentSwapGramDetNumerator dependent f1_3 (by decide) = 64
#guard GramSchmidt.Int.adjacentSwapGramDetQuotient dependent f1_3 (by decide) = 16

end GramSchmidtConformance
end Hex
