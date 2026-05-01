import HexGramSchmidtMathlib.Basic

/-!
Mathlib bridge conformance checks for `HexGramSchmidtMathlib`.

Oracle: none.
Mode: always.

Covered operations:
- `Hex.GramSchmidtMathlib.rowToEuclidean`
- `Hex.GramSchmidtMathlib.castRatMatrix`
- `Hex.GramSchmidtMathlib.castIntMatrix`
- `Hex.GramSchmidtMathlib.ratRowFamily`
- `Hex.GramSchmidtMathlib.intRowFamily`

Covered properties:
- rational rows convert coordinatewise into Mathlib's Euclidean space.
- rational matrices cast entrywise from `Rat` to `Real`.
- integer matrices cast entrywise from `Int` to `Rat`.
- rational row families are the explicit `rowToEuclidean` conversion of each row.
- integer row families agree with rational row families after `castIntMatrix`.

Covered edge cases:
- a typical nonsingular `3 x 3` rational matrix.
- a zero `2 x 2` integer and rational matrix.
- signed and fractional entries crossing the integer, rational, and real casts.
-/

namespace Hex
namespace GramSchmidtMathlibConformance

private def typicalRat : Matrix Rat 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 1 => 3
    | 1, 2 => 4
    | 2, 0 => 5
    | 2, 2 => 6
    | _, _ => 0

private def zeroRat : Matrix Rat 2 2 :=
  Matrix.ofFn fun _ _ => 0

private def signedFractionRat : Matrix Rat 2 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => (-3 : Rat) / 2
    | 0, 2 => 5
    | 1, 1 => (-7 : Rat) / 3
    | _, _ => 0

private def typicalInt : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 1 => 3
    | 1, 2 => 4
    | 2, 0 => 5
    | 2, 2 => 6
    | _, _ => 0

private def zeroInt : Matrix Int 2 2 :=
  Matrix.ofFn fun _ _ => 0

private def signedInt : Matrix Int 2 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => -3
    | 0, 2 => 5
    | 1, 1 => -7
    | _, _ => 0

private abbrev f0_3 : Fin 3 := ⟨0, by decide⟩
private abbrev f1_3 : Fin 3 := ⟨1, by decide⟩
private abbrev f2_3 : Fin 3 := ⟨2, by decide⟩
private abbrev f0_2 : Fin 2 := ⟨0, by decide⟩
private abbrev f1_2 : Fin 2 := ⟨1, by decide⟩

private example :
    (GramSchmidtMathlib.rowToEuclidean (typicalRat.row f0_3) : Fin 3 → ℝ) f1_3 = 2 := by
  norm_num [GramSchmidtMathlib.rowToEuclidean, typicalRat, Matrix.row, Matrix.ofFn]

private example :
    (GramSchmidtMathlib.rowToEuclidean (zeroRat.row f1_2) : Fin 2 → ℝ) f0_2 = 0 := by
  norm_num [GramSchmidtMathlib.rowToEuclidean, zeroRat, Matrix.row, Matrix.ofFn]

private example :
    (GramSchmidtMathlib.rowToEuclidean (signedFractionRat.row f0_2) : Fin 3 → ℝ) f0_3 =
      (-3 : ℝ) / 2 := by
  norm_num [GramSchmidtMathlib.rowToEuclidean, signedFractionRat, Matrix.row, Matrix.ofFn]

private example :
    (GramSchmidtMathlib.castRatMatrix typicalRat)[f2_3][f2_3] = (6 : ℝ) := by
  norm_num [GramSchmidtMathlib.castRatMatrix, typicalRat, Matrix.ofFn]

private example :
    (GramSchmidtMathlib.castRatMatrix zeroRat)[f1_2][f0_2] = (0 : ℝ) := by
  norm_num [GramSchmidtMathlib.castRatMatrix, zeroRat, Matrix.ofFn]

private example :
    (GramSchmidtMathlib.castRatMatrix signedFractionRat)[f1_2][f1_3] =
      (-7 : ℝ) / 3 := by
  norm_num [GramSchmidtMathlib.castRatMatrix, signedFractionRat, Matrix.ofFn]

#guard (GramSchmidtMathlib.castIntMatrix typicalInt)[f2_3][f0_3] = (5 : Rat)
#guard (GramSchmidtMathlib.castIntMatrix zeroInt)[f1_2][f1_2] = (0 : Rat)
#guard (GramSchmidtMathlib.castIntMatrix signedInt)[f1_2][f1_3] = (-7 : Rat)

private example :
    GramSchmidtMathlib.ratRowFamily typicalRat f1_3 =
      GramSchmidtMathlib.rowToEuclidean (typicalRat.row f1_3) := rfl

private example :
    GramSchmidtMathlib.ratRowFamily zeroRat f0_2 =
      GramSchmidtMathlib.rowToEuclidean (zeroRat.row f0_2) := rfl

private example :
    GramSchmidtMathlib.ratRowFamily signedFractionRat f1_2 =
      GramSchmidtMathlib.rowToEuclidean (signedFractionRat.row f1_2) := rfl

private example :
    GramSchmidtMathlib.intRowFamily typicalInt f2_3 =
      GramSchmidtMathlib.ratRowFamily (GramSchmidtMathlib.castIntMatrix typicalInt) f2_3 := rfl

private example :
    GramSchmidtMathlib.intRowFamily zeroInt f1_2 =
      GramSchmidtMathlib.ratRowFamily (GramSchmidtMathlib.castIntMatrix zeroInt) f1_2 := rfl

private example :
    GramSchmidtMathlib.intRowFamily signedInt f0_2 =
      GramSchmidtMathlib.ratRowFamily (GramSchmidtMathlib.castIntMatrix signedInt) f0_2 := rfl

end GramSchmidtMathlibConformance
end Hex
