import HexPoly.Division

/-!
Deterministic core conformance fixtures for `HexPoly`.

This module commits small replayable fixture data for the dense
normalization, arithmetic, and division surface. The checks are Lean-only
and use fixed serialized cases so later runners can reuse the same
inputs and expected outputs.
-/
namespace HexPoly

namespace Conformance

def library : String := "HexPoly"

def profile : String := "core"

def seed : Nat := 0

def polyInt (coeffs : List Int) : DensePoly Int :=
  DensePoly.ofArray coeffs.toArray

def polyRat (coeffs : List Rat) : DensePoly Rat :=
  DensePoly.ofArray coeffs.toArray

structure QueryFixture where
  name : String
  rawCoeffs : List Int
  coeffIndices : List Nat
  expectedNormalized : List Int
  expectedCoeffs : List Int
  expectedNatDegree? : Option Nat
  expectedDegree : Nat

def queryFixtures : List QueryFixture :=
  [ { name := "trim-trailing-zeros"
      rawCoeffs := [3, 0, -2, 0, 0]
      coeffIndices := [0, 1, 2, 3, 5]
      expectedNormalized := [3, 0, -2]
      expectedCoeffs := [3, 0, -2, 0, 0]
      expectedNatDegree? := some 2
      expectedDegree := 2 }
  , { name := "zero-polynomial"
      rawCoeffs := [0, 0, 0]
      coeffIndices := [0, 2]
      expectedNormalized := []
      expectedCoeffs := [0, 0]
      expectedNatDegree? := none
      expectedDegree := 0 }
  ]

def evalQueryFixture (fixture : QueryFixture) :
    String × List Int × List Int × Option Nat × Nat :=
  let p := polyInt fixture.rawCoeffs
  ( fixture.name
  , p.coeffs.toList
  , fixture.coeffIndices.map p.coeff
  , p.natDegree?
  , p.degree )

def arithmeticFixtures :
    List (String × List Int × List Int × List Int × List Int × List Int) :=
  [ ( "cancel-leading-zeros"
    , [1, 2, 0]
    , [-1, 3]
    , [0, 5]
    , [2, -1]
    , [-1, 1, 6] )
  , ( "normalize-after-add-sub-mul"
    , [0, 1]
    , [0, -1]
    , []
    , [0, 2]
    , [0, 0, -1] )
  ]

def evalArithmeticFixture
    (fixture : String × List Int × List Int × List Int × List Int × List Int) :
    String × List Int × List Int × List Int :=
  let (name, lhs, rhs, _, _, _) := fixture
  let p := polyInt lhs
  let q := polyInt rhs
  (name, (p + q).coeffs.toList, (p - q).coeffs.toList, (p * q).coeffs.toList)

def monicDivisionFixtures :
    List (String × List Int × List Int × List Int × List Int) :=
  [ ("exact-monic-division", [1, 2, 1], [1, 1], [1, 1], [])
  , ("monic-division-with-remainder", [1, 0, 1], [1, 1], [-1, 1], [2])
  ]

def evalMonicDivisionFixture
    (fixture : String × List Int × List Int × List Int × List Int) :
    String × List Int × List Int :=
  let (name, dividend, divisor, _, _) := fixture
  let result := DensePoly.divModMonic (polyInt dividend) (polyInt divisor)
  (name, result.quotient.coeffs.toList, result.remainder.coeffs.toList)

def fieldDivisionFixtures :
    List (String × List Rat × List Rat × List Rat × List Rat) :=
  [ ("exact-field-division", [1, 0, 1], [1, 1], [-1, 1], [2])
  , ("scaled-linear-divisor", [1, 0, 1], [2, 2], [(-1 : Rat) / 2, 1 / 2], [2]) ]

def evalFieldDivisionFixture
    (fixture : String × List Rat × List Rat × List Rat × List Rat) :
    String × List Rat × List Rat :=
  let (name, dividend, divisor, _, _) := fixture
  let result := DensePoly.divMod (polyRat dividend) (polyRat divisor)
  (name, result.quotient.coeffs.toList, result.remainder.coeffs.toList)

example : library = "HexPoly" := rfl

example : profile = "core" := rfl

example : seed = 0 := rfl

example :
    queryFixtures.map evalQueryFixture =
      [ ("trim-trailing-zeros", [3, 0, -2], [3, 0, -2, 0, 0], some 2, 2)
      , ("zero-polynomial", [], [0, 0], none, 0)
      ] := rfl

end Conformance

end HexPoly
