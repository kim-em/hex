import HexMatrix.Determinant
import HexMatrix.Nullspace

/-!
# `HexMatrix` benchmark fixtures

Stable benchmark cases for the first `HexMatrix` Phase 4 slice. This
module commits named determinant and row-reduction workloads together
with executable runners so later timing harnesses can import a
reproducible fixture registry directly from the library.
-/

namespace HexMatrix.Benchmark

/-- Stable identifiers for the committed Bareiss determinant cases. -/
inductive BareissCaseId
  | diagonal3
  | dense4
  | adversarial4
  deriving Repr, DecidableEq

/-- Stable identifiers for the committed row-reduction cases. -/
inductive RowReductionCaseId
  | rectangularSmall
  | pivotGap
  | denseMedium
  deriving Repr, DecidableEq

/-- Metadata for one committed Bareiss determinant benchmark case. -/
structure BareissCase where
  id : BareissCaseId
  name : String
  dimension : Nat
  deriving Repr

/-- Metadata for one committed RREF/nullspace benchmark case. -/
structure RowReductionCase where
  id : RowReductionCaseId
  name : String
  rows : Nat
  cols : Nat
  deriving Repr

/-- Materialized result for one Bareiss determinant benchmark case. -/
structure BareissResult where
  name : String
  dimension : Nat
  value : Int
  deriving Repr

/-- Materialized result for one committed RREF benchmark case. -/
structure RrefResult where
  name : String
  rows : Nat
  cols : Nat
  rank : Nat
  echelon : List (List Rat)
  transform : List (List Rat)
  pivotCols : List Nat
  deriving Repr

/-- Materialized result for one committed nullspace benchmark case. -/
structure NullspaceResult where
  name : String
  rows : Nat
  cols : Nat
  basis : List (List Rat)
  deriving Repr

private def serializeVector (v : Vector α n) : List α :=
  v.toList

private def serializeMatrix (M : Matrix α n m) : List (List α) :=
  M.toList.map serializeVector

private def serializePivotCols (v : Vector (Fin n) k) : List Nat :=
  v.toList.map Fin.val

private def serializeBasis (basis : Vector (Vector α n) k) : List (List α) :=
  basis.toList.map serializeVector

private def intRow3 (a0 a1 a2 : Int) : Vector Int 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else
      a2

private def intRow4 (a0 a1 a2 a3 : Int) : Vector Int 4 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else if i.1 = 2 then
      a2
    else
      a3

private def intMat33
    (a00 a01 a02 : Int)
    (a10 a11 a12 : Int)
    (a20 a21 a22 : Int) : Matrix Int 3 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      intRow3 a00 a01 a02
    else if i.1 = 1 then
      intRow3 a10 a11 a12
    else
      intRow3 a20 a21 a22

private def intMat44
    (a00 a01 a02 a03 : Int)
    (a10 a11 a12 a13 : Int)
    (a20 a21 a22 a23 : Int)
    (a30 a31 a32 a33 : Int) : Matrix Int 4 4 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      intRow4 a00 a01 a02 a03
    else if i.1 = 1 then
      intRow4 a10 a11 a12 a13
    else if i.1 = 2 then
      intRow4 a20 a21 a22 a23
    else
      intRow4 a30 a31 a32 a33

private def ratRow3 (a0 a1 a2 : Rat) : Vector Rat 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else
      a2

private def ratRow4 (a0 a1 a2 a3 : Rat) : Vector Rat 4 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else if i.1 = 2 then
      a2
    else
      a3

private def ratRow6 (a0 a1 a2 a3 a4 a5 : Rat) : Vector Rat 6 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else if i.1 = 2 then
      a2
    else if i.1 = 3 then
      a3
    else if i.1 = 4 then
      a4
    else
      a5

private def ratMat23
    (a00 a01 a02 : Rat)
    (a10 a11 a12 : Rat) : Matrix Rat 2 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      ratRow3 a00 a01 a02
    else
      ratRow3 a10 a11 a12

private def ratMat34
    (a00 a01 a02 a03 : Rat)
    (a10 a11 a12 a13 : Rat)
    (a20 a21 a22 a23 : Rat) : Matrix Rat 3 4 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      ratRow4 a00 a01 a02 a03
    else if i.1 = 1 then
      ratRow4 a10 a11 a12 a13
    else
      ratRow4 a20 a21 a22 a23

private def ratMat46
    (a00 a01 a02 a03 a04 a05 : Rat)
    (a10 a11 a12 a13 a14 a15 : Rat)
    (a20 a21 a22 a23 a24 a25 : Rat)
    (a30 a31 a32 a33 a34 a35 : Rat) : Matrix Rat 4 6 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      ratRow6 a00 a01 a02 a03 a04 a05
    else if i.1 = 1 then
      ratRow6 a10 a11 a12 a13 a14 a15
    else if i.1 = 2 then
      ratRow6 a20 a21 a22 a23 a24 a25
    else
      ratRow6 a30 a31 a32 a33 a34 a35

/--
Stable Bareiss determinant benchmark cases.

The committed inputs cover a diagonal warm-up, a dense `4 × 4` case,
and a singular-looking adversarial `4 × 4` workload.
-/
def bareissCases : List BareissCase :=
  [ { id := .diagonal3, name := "bareiss-diagonal-3x3", dimension := 3 }
  , { id := .dense4, name := "bareiss-dense-4x4", dimension := 4 }
  , { id := .adversarial4, name := "bareiss-adversarial-4x4", dimension := 4 }
  ]

/--
Stable row-reduction benchmark cases.

The cases cover a small rectangular matrix, a pivot-gap-shaped matrix,
and a denser medium rectangular matrix for the current `rref` and
nullspace extraction paths.
-/
def rowReductionCases : List RowReductionCase :=
  [ { id := .rectangularSmall, name := "row-reduction-rectangular-small", rows := 2, cols := 3 }
  , { id := .pivotGap, name := "row-reduction-pivot-gap", rows := 3, cols := 4 }
  , { id := .denseMedium, name := "row-reduction-dense-medium", rows := 4, cols := 6 }
  ]

private def runBareissById : BareissCaseId → Int
  | .diagonal3 =>
      Matrix.bareiss (intMat33 5 0 0 0 7 0 0 0 11)
  | .dense4 =>
      Matrix.bareiss (intMat44 3 1 4 1 5 9 2 6 5 3 5 8 9 7 9 3)
  | .adversarial4 =>
      Matrix.bareiss (intMat44 1 2 3 4 2 4 6 8 1 0 1 0 5 5 5 5)

private def runRrefById : RowReductionCaseId → RrefResult
  | .rectangularSmall =>
      let M := ratMat23 1 2 3 0 1 4
      let data := rref M
      { name := "row-reduction-rectangular-small"
      , rows := 2
      , cols := 3
      , rank := data.rank
      , echelon := serializeMatrix data.echelon
      , transform := serializeMatrix data.transform
      , pivotCols := serializePivotCols data.pivotCols
      }
  | .pivotGap =>
      let M := ratMat34 1 0 2 0 0 0 3 4 5 0 0 6
      let data := rref M
      { name := "row-reduction-pivot-gap"
      , rows := 3
      , cols := 4
      , rank := data.rank
      , echelon := serializeMatrix data.echelon
      , transform := serializeMatrix data.transform
      , pivotCols := serializePivotCols data.pivotCols
      }
  | .denseMedium =>
      let M := ratMat46 2 1 0 3 4 5 1 0 1 2 3 5 3 1 4 1 5 9 2 6 5 3 5 8
      let data := rref M
      { name := "row-reduction-dense-medium"
      , rows := 4
      , cols := 6
      , rank := data.rank
      , echelon := serializeMatrix data.echelon
      , transform := serializeMatrix data.transform
      , pivotCols := serializePivotCols data.pivotCols
      }

private def runNullspaceById : RowReductionCaseId → NullspaceResult
  | .rectangularSmall =>
      let M := ratMat23 1 2 3 0 1 4
      { name := "row-reduction-rectangular-small"
      , rows := 2
      , cols := 3
      , basis := serializeBasis (Matrix.nullspace M)
      }
  | .pivotGap =>
      let M := ratMat34 1 0 2 0 0 0 3 4 5 0 0 6
      { name := "row-reduction-pivot-gap"
      , rows := 3
      , cols := 4
      , basis := serializeBasis (Matrix.nullspace M)
      }
  | .denseMedium =>
      let M := ratMat46 2 1 0 3 4 5 1 0 1 2 3 5 3 1 4 1 5 9 2 6 5 3 5 8
      { name := "row-reduction-dense-medium"
      , rows := 4
      , cols := 6
      , basis := serializeBasis (Matrix.nullspace M)
      }

/-- Execute one committed Bareiss determinant benchmark case. -/
def runBareissCase (c : BareissCase) : BareissResult :=
  { name := c.name, dimension := c.dimension, value := runBareissById c.id }

/-- Execute one committed RREF benchmark case. -/
def runRrefCase (c : RowReductionCase) : RrefResult :=
  runRrefById c.id

/-- Execute one committed nullspace benchmark case. -/
def runNullspaceCase (c : RowReductionCase) : NullspaceResult :=
  runNullspaceById c.id

/-- Execute all committed Bareiss determinant benchmark cases. -/
def runBareissCases : List BareissResult :=
  bareissCases.map runBareissCase

/-- Execute all committed RREF benchmark cases. -/
def runRrefCases : List RrefResult :=
  rowReductionCases.map runRrefCase

/-- Execute all committed nullspace benchmark cases. -/
def runNullspaceCases : List NullspaceResult :=
  rowReductionCases.map runNullspaceCase

end HexMatrix.Benchmark
