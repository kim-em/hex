import HexGramSchmidt.GramDet
import HexGramSchmidt.Rat

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
  `Hex.GramSchmidt.Rat.basis`, `Hex.GramSchmidt.Rat.coeffs`,
  `Hex.GramSchmidt.Rat.gramDet`.
- **Covered properties:**
  - integer-input basis rows are the cast input rows on committed
    examples, including the `basis_zero` theorem;
  - both integer and rational coefficient matrices stay identity on
    committed examples, including `coeffs_diag` and `coeffs_upper`;
  - integer and rational Gram determinants match the leading Gram-matrix
    determinant on typical, edge, and adversarial fixtures;
  - integer `gramDetVec` packages the full prefix determinant sequence;
  - integer scaled coefficients agree with the determinant witnesses and
    the `scaledCoeffs_eq` theorem on committed lower-triangular entries;
  - integer `gramDet_eq_prod_normSq` matches the scaffolded
    `basisNormSqProduct` on committed examples.
- **Covered edge cases:** zero row prefixes, repeated rows producing a
  zero Gram determinant, the `k = 0` Gram-determinant convention, and
  diagonal/upper-triangular coefficient entries.
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

private def intRow2 (a0 a1 : Int) : Vector Int 2 :=
  Vector.ofFn fun i => if i.1 = 0 then a0 else a1

private def intRow3 (a0 a1 a2 : Int) : Vector Int 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else
      a2

private def ratRow2 (a0 a1 : Rat) : Vector Rat 2 :=
  Vector.ofFn fun i => if i.1 = 0 then a0 else a1

private def ratRow3 (a0 a1 a2 : Rat) : Vector Rat 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else
      a2

private def intMat22
    (a00 a01 : Int)
    (a10 a11 : Int) : Matrix Int 2 2 :=
  Vector.ofFn fun i => if i.1 = 0 then intRow2 a00 a01 else intRow2 a10 a11

private def intMat32
    (a00 a01 : Int)
    (a10 a11 : Int)
    (a20 a21 : Int) : Matrix Int 3 2 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      intRow2 a00 a01
    else if i.1 = 1 then
      intRow2 a10 a11
    else
      intRow2 a20 a21

private def ratMat22
    (a00 a01 : Rat)
    (a10 a11 : Rat) : Matrix Rat 2 2 :=
  Vector.ofFn fun i => if i.1 = 0 then ratRow2 a00 a01 else ratRow2 a10 a11

private def ratMat32
    (a00 a01 : Rat)
    (a10 a11 : Rat)
    (a20 a21 : Rat) : Matrix Rat 3 2 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      ratRow2 a00 a01
    else if i.1 = 1 then
      ratRow2 a10 a11
    else
      ratRow2 a20 a21

private def intTypical : Matrix Int 3 2 :=
  intMat32 1 2 0 3 4 5

private def intEdge : Matrix Int 2 2 :=
  intMat22 1 0 0 1

private def intAdversarial : Matrix Int 2 2 :=
  intMat22 1 2 1 2

private def ratTypical : Matrix Rat 3 2 :=
  ratMat32 1 2 (3 / 2) (-1) 0 5

private def ratEdge : Matrix Rat 2 2 :=
  ratMat22 1 0 0 1

private def ratAdversarial : Matrix Rat 2 2 :=
  ratMat22 1 2 1 2

/-! ## Integer basis and coefficients -/

example :
    Matrix.row (GramSchmidt.Int.basis intTypical) 1 = ratRow2 0 3 := by
  rfl

example :
    Matrix.row (GramSchmidt.Int.basis intEdge) 1 = ratRow2 0 1 := by
  rfl

#guard serializeRatMatrix (GramSchmidt.Int.coeffs intTypical) =
  [[1, 0, 0], [0, 1, 0], [0, 0, 1]]

#guard serializeRatMatrix (GramSchmidt.Int.coeffs intAdversarial) =
  [[1, 0], [0, 1]]

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

/-! ## Rational basis, coefficients, and Gram determinants -/

example :
    Matrix.row (GramSchmidt.Rat.basis ratTypical) 1 = ratRow2 (3 / 2) (-1) := by
  rfl

example :
    Matrix.row (GramSchmidt.Rat.basis ratEdge) 1 = ratRow2 0 1 := by
  rfl

example :
    Matrix.entry (GramSchmidt.Rat.coeffs ratTypical) 2 2 = 1 := by
  rfl

example :
    Matrix.entry (GramSchmidt.Rat.coeffs ratAdversarial) 0 1 = 0 := by
  rfl

#guard GramSchmidt.Rat.gramDet ratTypical 0 (by decide) = 1
#guard GramSchmidt.Rat.gramDet ratTypical 1 (by decide) = 5
#guard GramSchmidt.Rat.gramDet ratTypical 2 (by decide) = 16
#guard GramSchmidt.Rat.gramDet ratEdge 2 (by decide) = 1
#guard GramSchmidt.Rat.gramDet ratAdversarial 2 (by decide) = 0

end
end Conformance
end HexGramSchmidt
