import HexMatrix.RowOps

/-!
Deterministic core conformance fixtures for `HexMatrix`.

This module commits small replayable fixture data for the determinant
and elementary row-operation surface. The checks are Lean-only and use
fixed serialized cases so later runners can reuse the same inputs and
expected outputs.
-/
namespace HexMatrix

namespace Conformance

def library : String := "HexMatrix"

def profile : String := "core"

def seed : Nat := 0

def serializeMatrix (M : Matrix Int n m) : List (List Int) :=
  M.toList.map Vector.toList

def intRow2 (a0 a1 : Int) : Vector Int 2 :=
  Vector.ofFn fun i => if i.1 = 0 then a0 else a1

def intRow3 (a0 a1 a2 : Int) : Vector Int 3 :=
  Vector.ofFn fun i =>
    if i.1 = 0 then
      a0
    else if i.1 = 1 then
      a1
    else
      a2

def intMat2
    (a00 a01 : Int)
    (a10 a11 : Int) : Matrix Int 2 2 :=
  Vector.ofFn fun i => if i.1 = 0 then intRow2 a00 a01 else intRow2 a10 a11

def intMat3
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

def fin2_0 : Fin 2 := ⟨0, by decide⟩
def fin2_1 : Fin 2 := ⟨1, by decide⟩

def fin3_0 : Fin 3 := ⟨0, by decide⟩
def fin3_1 : Fin 3 := ⟨1, by decide⟩
def fin3_2 : Fin 3 := ⟨2, by decide⟩

structure Determinant2Fixture where
  name : String
  rawRows : List (List Int)
  matrix : Matrix Int 2 2
  expectedDet : Int
  expectedBareiss : Int

def determinant2Fixtures : List Determinant2Fixture :=
  [ { name := "identity-2x2"
      rawRows := [[1, 0], [0, 1]]
      matrix := intMat2 1 0 0 1
      expectedDet := 1
      expectedBareiss := 1 }
  , { name := "singular-2x2"
      rawRows := [[1, 2], [2, 4]]
      matrix := intMat2 1 2 2 4
      expectedDet := 0
      expectedBareiss := 0 }
  ]

def evalDeterminant2Fixture (fixture : Determinant2Fixture) :
    String × List (List Int) × Int × Int :=
  ( fixture.name
  , serializeMatrix fixture.matrix
  , Matrix.det fixture.matrix
  , Matrix.bareiss fixture.matrix )

structure Determinant3Fixture where
  name : String
  rawRows : List (List Int)
  matrix : Matrix Int 3 3
  expectedDet : Int
  expectedBareiss : Int

def determinant3Fixtures : List Determinant3Fixture :=
  [ { name := "upper-coupled-3x3"
      rawRows := [[2, 1, 0], [1, 3, 4], [0, 2, 5]]
      matrix := intMat3 2 1 0 1 3 4 0 2 5
      expectedDet := 9
      expectedBareiss := 9 }
  ]

def evalDeterminant3Fixture (fixture : Determinant3Fixture) :
    String × List (List Int) × Int × Int :=
  ( fixture.name
  , serializeMatrix fixture.matrix
  , Matrix.det fixture.matrix
  , Matrix.bareiss fixture.matrix )

structure RowSwapFixture where
  name : String
  rawRows : List (List Int)
  matrix : Matrix Int 3 3
  swapI : Fin 3
  swapJ : Fin 3
  expectedMatrix : List (List Int)
  expectedDetBefore : Int
  expectedDetAfter : Int

def rowSwapFixtures : List RowSwapFixture :=
  [ { name := "swap-outer-rows"
      rawRows := [[2, 1, 0], [1, 3, 4], [0, 2, 5]]
      matrix := intMat3 2 1 0 1 3 4 0 2 5
      swapI := fin3_0
      swapJ := fin3_2
      expectedMatrix := [[0, 2, 5], [1, 3, 4], [2, 1, 0]]
      expectedDetBefore := 9
      expectedDetAfter := -9 }
  ]

def evalRowSwapFixture (fixture : RowSwapFixture) :
    String × Int × List (List Int) × Int :=
  let swapped := Matrix.rowSwap fixture.matrix fixture.swapI fixture.swapJ
  ( fixture.name
  , Matrix.det fixture.matrix
  , serializeMatrix swapped
  , Matrix.det swapped )

structure RowScaleFixture where
  name : String
  rawRows : List (List Int)
  matrix : Matrix Int 3 3
  row : Fin 3
  scale : Int
  expectedMatrix : List (List Int)
  expectedDetBefore : Int
  expectedDetAfter : Int

def rowScaleFixtures : List RowScaleFixture :=
  [ { name := "scale-middle-row"
      rawRows := [[2, 1, 0], [1, 3, 4], [0, 2, 5]]
      matrix := intMat3 2 1 0 1 3 4 0 2 5
      row := fin3_1
      scale := -2
      expectedMatrix := [[2, 1, 0], [-2, -6, -8], [0, 2, 5]]
      expectedDetBefore := 9
      expectedDetAfter := -18 }
  ]

def evalRowScaleFixture (fixture : RowScaleFixture) :
    String × Int × List (List Int) × Int :=
  let scaled := Matrix.rowScale fixture.matrix fixture.row fixture.scale
  ( fixture.name
  , Matrix.det fixture.matrix
  , serializeMatrix scaled
  , Matrix.det scaled )

structure RowAddFixture where
  name : String
  rawRows : List (List Int)
  matrix : Matrix Int 3 3
  target : Fin 3
  source : Fin 3
  scale : Int
  expectedMatrix : List (List Int)
  expectedDetBefore : Int
  expectedDetAfter : Int

def rowAddFixtures : List RowAddFixture :=
  [ { name := "add-three-times-top-row"
      rawRows := [[2, 1, 0], [1, 3, 4], [0, 2, 5]]
      matrix := intMat3 2 1 0 1 3 4 0 2 5
      target := fin3_2
      source := fin3_0
      scale := 3
      expectedMatrix := [[2, 1, 0], [1, 3, 4], [6, 5, 5]]
      expectedDetBefore := 9
      expectedDetAfter := 9 }
  ]

def evalRowAddFixture (fixture : RowAddFixture) :
    String × Int × List (List Int) × Int :=
  let added := Matrix.rowAdd fixture.matrix fixture.target fixture.source fixture.scale
  ( fixture.name
  , Matrix.det fixture.matrix
  , serializeMatrix added
  , Matrix.det added )

example : library = "HexMatrix" := rfl

example : profile = "core" := rfl

example : seed = 0 := rfl

example :
    determinant2Fixtures.map evalDeterminant2Fixture =
      [ ("identity-2x2", [[1, 0], [0, 1]], 1, 1)
      , ("singular-2x2", [[1, 2], [2, 4]], 0, 0)
      ] := by decide

example :
    determinant3Fixtures.map evalDeterminant3Fixture =
      [("upper-coupled-3x3", [[2, 1, 0], [1, 3, 4], [0, 2, 5]], 9, 9)] := by decide

example :
    rowSwapFixtures.map evalRowSwapFixture =
      [("swap-outer-rows", 9, [[0, 2, 5], [1, 3, 4], [2, 1, 0]], -9)] := by decide

example :
    rowScaleFixtures.map evalRowScaleFixture =
      [("scale-middle-row", 9, [[2, 1, 0], [-2, -6, -8], [0, 2, 5]], -18)] := by decide

example :
    rowAddFixtures.map evalRowAddFixture =
      [("add-three-times-top-row", 9, [[2, 1, 0], [1, 3, 4], [6, 5, 5]], 9)] := by decide

end Conformance

end HexMatrix
