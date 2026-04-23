import HexPoly.Gcd

/-!
# `HexPoly` benchmark fixtures

Stable benchmark cases for the first `HexPoly` Phase 4 slice. This
module commits named multiplication, monic-division, and GCD/XGCD
workloads together with executable runners so later timing harnesses
can import a reproducible fixture registry directly from the library.
-/

namespace HexPoly.Benchmark

/-- Stable identifiers for the committed multiplication cases. -/
inductive MulCaseId
  | smallDense
  | mediumSparse
  deriving Repr, DecidableEq

/-- Stable identifiers for the committed monic-division cases. -/
inductive DivModMonicCaseId
  | smallExact
  | mediumInexact
  deriving Repr, DecidableEq

/-- Stable identifiers for the committed GCD/XGCD cases. -/
inductive GcdCaseId
  | smallLinear
  | mediumQuadratic
  deriving Repr, DecidableEq

/-- Metadata for one committed multiplication benchmark case. -/
structure MulCase where
  id : MulCaseId
  name : String
  leftDegree : Nat
  rightDegree : Nat
  deriving Repr

/-- Metadata for one committed monic-division benchmark case. -/
structure DivModMonicCase where
  id : DivModMonicCaseId
  name : String
  dividendDegree : Nat
  divisorDegree : Nat
  deriving Repr

/-- Metadata for one committed GCD/XGCD benchmark case. -/
structure GcdCase where
  id : GcdCaseId
  name : String
  leftDegree : Nat
  rightDegree : Nat
  deriving Repr

/-- Materialized result for one multiplication benchmark case. -/
structure MulResult where
  name : String
  coeffs : List Int
  deriving Repr

/-- Materialized result for one monic-division benchmark case. -/
structure DivModMonicResult where
  name : String
  quotient : List Int
  remainder : List Int
  deriving Repr

/-- Materialized result for one GCD/XGCD benchmark case. -/
structure GcdResult where
  name : String
  gcd : List Rat
  s : List Rat
  t : List Rat
  deriving Repr

/-- Render a list of `Int` coefficients as one stable CSV field. -/
def renderIntListField (coeffs : List Int) : String :=
  ";".intercalate (coeffs.map toString)

/-- Render a list of `Rat` coefficients as one stable CSV field. -/
def renderRatListField (coeffs : List Rat) : String :=
  ";".intercalate (coeffs.map toString)

/-- Render one multiplication benchmark result as a stable CSV row. -/
def MulResult.toCsvRow (result : MulResult) : String :=
  ",".intercalate
    [ result.name
    , renderIntListField result.coeffs
    ]

/-- Header shared by the multiplication CSV runner. -/
def mulCsvHeader : String :=
  "name,coeffs"

/-- Render one monic-division benchmark result as a stable CSV row. -/
def DivModMonicResult.toCsvRow (result : DivModMonicResult) : String :=
  ",".intercalate
    [ result.name
    , renderIntListField result.quotient
    , renderIntListField result.remainder
    ]

/-- Header shared by the monic-division CSV runner. -/
def divModMonicCsvHeader : String :=
  "name,quotient,remainder"

/-- Render one GCD/XGCD benchmark result as a stable CSV row. -/
def GcdResult.toCsvRow (result : GcdResult) : String :=
  ",".intercalate
    [ result.name
    , renderRatListField result.gcd
    , renderRatListField result.s
    , renderRatListField result.t
    ]

/-- Header shared by the GCD/XGCD CSV runner. -/
def gcdCsvHeader : String :=
  "name,gcd,s,t"

private def intCoeffs (p : HexPoly.DensePoly Int) : List Int :=
  p.coeffs.toList

private def ratCoeffs (p : HexPoly.DensePoly Rat) : List Rat :=
  p.coeffs.toList

private def intPoly (coeffs : List Int) : HexPoly.DensePoly Int :=
  HexPoly.DensePoly.ofArray coeffs.toArray

private def ratPoly (coeffs : List Rat) : HexPoly.DensePoly Rat :=
  HexPoly.DensePoly.ofArray coeffs.toArray

/--
Stable multiplication benchmark cases.

The committed inputs cover a small dense warm-up and a larger sparse
shape that still exercises the full schoolbook convolution path.
-/
def mulCases : List MulCase :=
  [ { id := .smallDense, name := "mul-small-dense", leftDegree := 2, rightDegree := 2 }
  , { id := .mediumSparse, name := "mul-medium-sparse", leftDegree := 6, rightDegree := 5 }
  ]

/--
Stable monic-division benchmark cases.

The cases cover one exact linear-factor division and one larger inexact
division where the remainder stays nonzero.
-/
def divModMonicCases : List DivModMonicCase :=
  [ { id := .smallExact, name := "divmodmonic-small-exact", dividendDegree := 3, divisorDegree := 1 }
  , { id := .mediumInexact, name := "divmodmonic-medium-inexact", dividendDegree := 6, divisorDegree := 2 }
  ]

/--
Stable GCD/XGCD benchmark cases.

The committed field-valued inputs cover a small shared linear factor and
one larger pair with a quadratic common factor.
-/
def gcdCases : List GcdCase :=
  [ { id := .smallLinear, name := "gcd-small-linear", leftDegree := 2, rightDegree := 1 }
  , { id := .mediumQuadratic, name := "gcd-medium-quadratic", leftDegree := 4, rightDegree := 3 }
  ]

private def runMulById : MulCaseId → MulResult
  | .smallDense =>
      let left := intPoly [3, -1, 2]
      let right := intPoly [1, 4, -2]
      { name := "mul-small-dense"
      , coeffs := intCoeffs (left * right)
      }
  | .mediumSparse =>
      let left := intPoly [5, 0, -3, 1, 0, 2, 4]
      let right := intPoly [-2, 7, 0, 0, 1, 3]
      { name := "mul-medium-sparse"
      , coeffs := intCoeffs (left * right)
      }

private def runDivModMonicById : DivModMonicCaseId → DivModMonicResult
  | .smallExact =>
      let dividend := intPoly [2, -3, 0, 1]
      let divisor := intPoly [-1, 1]
      let result := HexPoly.DensePoly.divModMonic dividend divisor
      { name := "divmodmonic-small-exact"
      , quotient := intCoeffs result.quotient
      , remainder := intCoeffs result.remainder
      }
  | .mediumInexact =>
      let dividend := intPoly [4, -1, 0, 3, 2, -2, 1]
      let divisor := intPoly [1, 0, 1]
      let result := HexPoly.DensePoly.divModMonic dividend divisor
      { name := "divmodmonic-medium-inexact"
      , quotient := intCoeffs result.quotient
      , remainder := intCoeffs result.remainder
      }

private def runGcdById : GcdCaseId → GcdResult
  | .smallLinear =>
      let left := ratPoly [(-1 : Rat), 0, 1]
      let right := ratPoly [(-1 : Rat), 1]
      let result := HexPoly.DensePoly.xgcd left right
      { name := "gcd-small-linear"
      , gcd := ratCoeffs result.gcd
      , s := ratCoeffs result.s
      , t := ratCoeffs result.t
      }
  | .mediumQuadratic =>
      let common := ratPoly [2, -3, 1]
      let left := common * ratPoly [(-1 : Rat), 0, 2]
      let right := common * ratPoly [3, 1]
      let result := HexPoly.DensePoly.xgcd left right
      { name := "gcd-medium-quadratic"
      , gcd := ratCoeffs result.gcd
      , s := ratCoeffs result.s
      , t := ratCoeffs result.t
      }

/-- Run one committed multiplication benchmark case. -/
def runMulCase (c : MulCase) : MulResult :=
  runMulById c.id

/-- Run one committed monic-division benchmark case. -/
def runDivModMonicCase (c : DivModMonicCase) : DivModMonicResult :=
  runDivModMonicById c.id

/-- Run one committed GCD/XGCD benchmark case. -/
def runGcdCase (c : GcdCase) : GcdResult :=
  runGcdById c.id

/-- Run all committed multiplication benchmark cases. -/
def runMulBenchmarks : List MulResult :=
  mulCases.map runMulCase

/-- Run all committed monic-division benchmark cases. -/
def runDivModMonicBenchmarks : List DivModMonicResult :=
  divModMonicCases.map runDivModMonicCase

/-- Run all committed GCD/XGCD benchmark cases. -/
def runGcdBenchmarks : List GcdResult :=
  gcdCases.map runGcdCase

/-- Run all committed multiplication cases and return CSV-style rows. -/
def runMulCsv : List String :=
  mulCsvHeader :: runMulBenchmarks.map MulResult.toCsvRow

/-- Run all committed monic-division cases and return CSV-style rows. -/
def runDivModMonicCsv : List String :=
  divModMonicCsvHeader :: runDivModMonicBenchmarks.map DivModMonicResult.toCsvRow

/-- Run all committed GCD/XGCD cases and return CSV-style rows. -/
def runGcdCsv : List String :=
  gcdCsvHeader :: runGcdBenchmarks.map GcdResult.toCsvRow

end HexPoly.Benchmark
