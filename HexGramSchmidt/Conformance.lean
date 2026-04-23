import HexGramSchmidt.GramDet
import HexGramSchmidt.Rat
import HexGramSchmidt.Update

/-!
# `HexGramSchmidt` -- core conformance

Deterministic Lean-only conformance checks for the foundational
Gram-Schmidt basis, coefficient, and Gram-determinant surface.

**Conformance contract for this slice:**

- **Oracle:** `none`.
- **Mode:** `always`.
- **Covered operations:** `Hex.GramSchmidt.Int.basis`,
  `Hex.GramSchmidt.Int.coeffs`, `Hex.GramSchmidt.Int.gramDet`,
  `Hex.GramSchmidt.Int.gramDetVec`, `Hex.GramSchmidt.Int.scaledCoeffs`,
  `Hex.GramSchmidt.Rat.gramDet`.
- **Covered properties:**
  - integer-input basis satisfies the theorem-backed `basis_zero`
    contract on committed fixtures;
  - integer coefficient checks stay on the theorem-backed diagonal and
    upper-triangular shape guarantees, including `coeffs_diag` and
    `coeffs_upper`;
- rational Gram determinants match the leading Gram-matrix determinant
  on typical, edge, and adversarial fixtures;
- integer Gram determinants match the leading Gram-matrix
  determinant on typical, edge, and adversarial fixtures;
  - integer `gramDetVec` packages the full prefix determinant sequence;
  - integer scaled coefficients agree with the determinant witnesses and
    the `scaledCoeffs_eq` theorem on committed lower-triangular entries;
  - integer `gramDet_eq_prod_normSq` matches the scaffolded
    `basisNormSqProduct` on committed examples.
- **Covered edge cases:** zero row prefixes, repeated rows producing a
  zero Gram determinant, the `k = 0` Gram-determinant convention, and
  integer diagonal/upper-triangular coefficient entries.
-/

namespace HexGramSchmidt
namespace Conformance

open HexMatrix
open Hex

noncomputable section

private def serializeVector (v : Vector α n) : List α :=
  v.toList

private def serializeMatrix (M : Matrix α n m) : List (List α) :=
  M.toList.map serializeVector

private def serializeRatMatrix (M : Matrix Rat n m) : List (List Rat) :=
  serializeMatrix M

private def vectorOfList! [Inhabited α] (xs : List α) : Vector α n :=
  (Vector.ofList? (n := n) xs).get!

private def matrixOfList2D! [Inhabited α] (rows : List (List α)) : Matrix α n m :=
  (Matrix.ofList2D (n := n) (m := m) rows).get!

private def intTypical : Matrix Int 3 2 :=
  matrixOfList2D! [[1, 2], [0, 3], [4, 5]]

private def intEdge : Matrix Int 2 2 :=
  matrixOfList2D! [[1, 0], [0, 1]]

private def intAdversarial : Matrix Int 2 2 :=
  matrixOfList2D! [[1, 2], [1, 2]]

private def intGramSchmidtCase : Matrix Int 2 2 :=
  matrixOfList2D! [[1, 0], [1, 1]]

private def ratTypical : Matrix Rat 3 2 :=
  matrixOfList2D! [[1, 2], [3 / 2, -1], [0, 5]]

private def ratEdge : Matrix Rat 2 2 :=
  matrixOfList2D! [[1, 0], [0, 1]]

private def ratAdversarial : Matrix Rat 2 2 :=
  matrixOfList2D! [[1, 2], [1, 2]]

private def sizeReduceTypical : Matrix Int 3 3 :=
  matrixOfList2D! [[5, -1, 2], [0, 3, 4], [7, 8, -6]]

private def sizeReduceEdge : Matrix Int 2 3 :=
  matrixOfList2D! [[0, 0, 0], [0, 0, 0]]

private def sizeReduceAdversarial : Matrix Int 3 2 :=
  matrixOfList2D! [[2, -3], [2, -3], [-5, 11]]

private def adjacentSwapTypical : Matrix Int 3 2 :=
  matrixOfList2D! [[1, 2], [3, 4], [5, 6]]

private def adjacentSwapEdge : Matrix Int 2 2 :=
  matrixOfList2D! [[9, -2], [4, 7]]

private def adjacentSwapAdversarial : Matrix Int 3 2 :=
  matrixOfList2D! [[4, -1], [4, -1], [-8, 5]]

/-! ## Integer basis and coefficients -/

example :
    Matrix.row (GramSchmidt.Int.basis intTypical) 0 =
      GramSchmidt.Int.castRow (Matrix.row intTypical 0) := by
  simpa using GramSchmidt.Int.basis_zero intTypical (by decide)

example :
    Matrix.entry (GramSchmidt.Int.coeffs intTypical) 1 1 = 1 := by
  simpa using GramSchmidt.Int.coeffs_diag intTypical 1 (by decide)

example :
    Matrix.entry (GramSchmidt.Int.coeffs intTypical) 1 2 = 0 := by
  simpa using GramSchmidt.Int.coeffs_upper intTypical 1 2 (by decide) (by decide) (by decide)

example :
    Matrix.dot (Matrix.row (GramSchmidt.Int.basis intGramSchmidtCase) 0)
      (Matrix.row (GramSchmidt.Int.basis intGramSchmidtCase) 1) = 0 := by
  simpa using
    GramSchmidt.Int.basis_orthogonal intGramSchmidtCase 0 1 (by decide) (by decide) (by decide)

example :
    Matrix.entry (GramSchmidt.Int.coeffs intGramSchmidtCase) 1 0 =
      GramSchmidt.Int.projCoeff
        (GramSchmidt.Int.castRow (Matrix.row intGramSchmidtCase 1))
        (GramSchmidt.Int.basisRow intGramSchmidtCase 0) := by
  change
    GramSchmidt.Int.projCoeff
      (GramSchmidt.Int.castRow (Matrix.row intGramSchmidtCase 1))
      (GramSchmidt.Int.basisRow intGramSchmidtCase 0) =
    GramSchmidt.Int.projCoeff
      (GramSchmidt.Int.castRow (Matrix.row intGramSchmidtCase 1))
      (GramSchmidt.Int.basisRow intGramSchmidtCase 0)
  rfl

/-! ## Integer Gram determinants -/

#guard GramSchmidt.Int.gramDet intTypical 0 (by decide) = 1
#guard GramSchmidt.Int.gramDet intTypical 1 (by decide) = 5
#guard GramSchmidt.Int.gramDet intTypical 2 (by decide) = 9
#guard GramSchmidt.Int.gramDet intEdge 2 (by decide) = 1
#guard GramSchmidt.Int.gramDet intAdversarial 2 (by decide) = 0

#guard (GramSchmidt.Int.gramDetVec intTypical).toList = [1, 5, 9, 0]
#guard (GramSchmidt.Int.gramDetVec intEdge).toList = [1, 1, 1]
#guard (GramSchmidt.Int.gramDetVec intAdversarial).toList = [1, 5, 0]

example :
    (GramSchmidt.Int.gramDet intTypical 2 (by decide) : Rat) =
      GramSchmidt.Int.basisNormSqProduct intTypical 2 := by
  simpa using
    (GramSchmidt.Int.gramDet_eq_prod_normSq intTypical trivial 2 (by decide))

/-! ## Integer scaled coefficients -/

#guard serializeMatrix (GramSchmidt.Int.scaledCoeffs intTypical) =
  [[0, 0, 0], [6, 0, 0], [14, -9, 0]]

#guard serializeMatrix (GramSchmidt.Int.scaledCoeffs intEdge) =
  [[0, 0], [0, 0]]

#guard serializeMatrix (GramSchmidt.Int.scaledCoeffs intAdversarial) =
  [[0, 0], [5, 0]]

example :
    ((Matrix.entry (GramSchmidt.Int.scaledCoeffs intTypical) 2 1 : Int) : Rat) =
      (GramSchmidt.Int.gramDet intTypical 2 (by decide) : Rat) *
        Matrix.entry (GramSchmidt.Int.coeffs intTypical) 2 1 := by
  simpa using GramSchmidt.Int.scaledCoeffs_eq intTypical 2 1 (by decide) (by decide)

/-! ## Rational Gram determinants -/

#guard GramSchmidt.Rat.gramDet ratTypical 0 (by decide) = 1
#guard GramSchmidt.Rat.gramDet ratTypical 1 (by decide) = 5
#guard GramSchmidt.Rat.gramDet ratTypical 2 (by decide) = 16
#guard GramSchmidt.Rat.gramDet ratEdge 2 (by decide) = 1
#guard GramSchmidt.Rat.gramDet ratAdversarial 2 (by decide) = 0

/-! ## Integer row operations -/

#guard GramSchmidt.Int.sizeReduce sizeReduceTypical 2 0 3 =
  Matrix.rowAdd sizeReduceTypical ⟨2, by decide⟩ ⟨0, by decide⟩ (-3)

#guard GramSchmidt.Int.sizeReduce sizeReduceEdge 2 0 7 = sizeReduceEdge

#guard GramSchmidt.Int.sizeReduce sizeReduceAdversarial 2 3 (-2) =
  sizeReduceAdversarial

#guard GramSchmidt.Int.sizeReduce sizeReduceAdversarial 1 0 (-2) =
  Matrix.rowAdd sizeReduceAdversarial ⟨1, by decide⟩ ⟨0, by decide⟩ 2

#guard GramSchmidt.Int.adjacentSwap adjacentSwapTypical 2 =
  Matrix.rowSwap adjacentSwapTypical ⟨2, by decide⟩ ⟨1, by decide⟩

#guard GramSchmidt.Int.adjacentSwap adjacentSwapEdge 0 = adjacentSwapEdge

#guard GramSchmidt.Int.adjacentSwap adjacentSwapAdversarial 3 =
  adjacentSwapAdversarial

#guard GramSchmidt.Int.adjacentSwap adjacentSwapAdversarial 1 =
  Matrix.rowSwap adjacentSwapAdversarial ⟨1, by decide⟩ ⟨0, by decide⟩

end
end Conformance
end HexGramSchmidt
