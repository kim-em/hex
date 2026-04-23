import HexArith.Barrett.Context
import HexArith.ExtGcd
import HexArith.Montgomery.Context
import HexArith.PowMod

/-!
# `HexArith` benchmark fixtures

Stable benchmark cases for the first `HexArith` Phase 4 slice. This
module commits named inputs and executable runners for the current
microbenchmarks so later timing harnesses can import a reproducible
fixture registry directly from the library.
-/

namespace HexArith.Benchmark

/-- Named `Nat` extended-GCD benchmark case. -/
structure NatExtGcdCase where
  name : String
  a : Nat
  b : Nat

/-- Named `Int` extended-GCD benchmark case. -/
structure IntExtGcdCase where
  name : String
  a : Int
  b : Int

/-- Named `UInt64` extended-GCD benchmark case. -/
structure UInt64ExtGcdCase where
  name : String
  a : UInt64
  b : UInt64

/-- Named modular-exponentiation benchmark case. -/
structure PowModCase where
  name : String
  a : Nat
  n : Nat
  p : Nat

/-- Materialized result of a `Nat` extended-GCD benchmark case. -/
structure NatExtGcdResult where
  name : String
  gcd : Nat
  s : Int
  t : Int

/-- Materialized result of an `Int` extended-GCD benchmark case. -/
structure IntExtGcdResult where
  name : String
  gcd : Nat
  s : Int
  t : Int

/-- Materialized result of a `UInt64` extended-GCD benchmark case. -/
structure UInt64ExtGcdResult where
  name : String
  gcd : UInt64
  s : Int
  t : Int

/-- Materialized result of a modular-exponentiation benchmark case. -/
structure PowModResult where
  name : String
  value : Nat

/-- Which reduction path a committed comparison case is meant to highlight. -/
inductive ReductionPreference
  | barrett
  | montgomery
  | crossover
  deriving Repr, DecidableEq

/-- Stable identifiers for the committed reduction comparison cases. -/
inductive ReductionComparisonCaseId
  | barrettTiny
  | barrettUpperEdge
  | montgomeryCrossover
  deriving Repr, DecidableEq

/--
Named Barrett-versus-Montgomery comparison case.

The runner dispatches by `ReductionComparisonCaseId`, which lets the
implementation construct proof-carrying Barrett and Montgomery contexts
for each committed modulus directly.
-/
structure ReductionComparisonCase where
  id : ReductionComparisonCaseId
  name : String
  modulus : UInt64
  a : UInt64
  b : UInt64
  preference : ReductionPreference

/-- Materialized result for one reduction-path measurement case. -/
structure ReductionComparisonResult where
  name : String
  modulus : UInt64
  a : UInt64
  b : UInt64
  preference : ReductionPreference
  barrettValue? : Option UInt64
  montgomeryValue? : Option UInt64

/-- Render the committed reduction preference as a stable CSV token. -/
def ReductionPreference.csvTag : ReductionPreference → String
  | .barrett => "barrett"
  | .montgomery => "montgomery"
  | .crossover => "crossover"

/-- Render an optional `UInt64` result field for CSV-style output. -/
def renderUInt64Field (value? : Option UInt64) : String :=
  match value? with
  | some value => toString value.toNat
  | none => "NA"

/-- Render one `Nat` extended-GCD result as a stable CSV row. -/
def NatExtGcdResult.toCsvRow (result : NatExtGcdResult) : String :=
  ",".intercalate
    [ result.name
    , toString result.gcd
    , toString result.s
    , toString result.t
    ]

/-- Header shared by the `Nat` extended-GCD CSV runner. -/
def natExtGcdCsvHeader : String :=
  "name,gcd,s,t"

/-- Render one `Int` extended-GCD result as a stable CSV row. -/
def IntExtGcdResult.toCsvRow (result : IntExtGcdResult) : String :=
  ",".intercalate
    [ result.name
    , toString result.gcd
    , toString result.s
    , toString result.t
    ]

/-- Header shared by the `Int` extended-GCD CSV runner. -/
def intExtGcdCsvHeader : String :=
  "name,gcd,s,t"

/-- Render one `UInt64` extended-GCD result as a stable CSV row. -/
def UInt64ExtGcdResult.toCsvRow (result : UInt64ExtGcdResult) : String :=
  ",".intercalate
    [ result.name
    , toString result.gcd.toNat
    , toString result.s
    , toString result.t
    ]

/-- Header shared by the `UInt64` extended-GCD CSV runner. -/
def uint64ExtGcdCsvHeader : String :=
  "name,gcd,s,t"

/-- Render one modular-exponentiation result as a stable CSV row. -/
def PowModResult.toCsvRow (result : PowModResult) : String :=
  ",".intercalate
    [ result.name
    , toString result.value
    ]

/-- Header shared by the modular-exponentiation CSV runner. -/
def powModCsvHeader : String :=
  "name,value"

/--
Serialize one comparison result as a stable machine-readable row.

The output is intentionally simple CSV so later benchmark scripts can
ingest it without having to parse Lean `repr` output.
-/
def ReductionComparisonResult.toCsvRow (result : ReductionComparisonResult) : String :=
  ",".intercalate
    [ result.name
    , toString result.modulus.toNat
    , toString result.a.toNat
    , toString result.b.toNat
    , result.preference.csvTag
    , renderUInt64Field result.barrettValue?
    , renderUInt64Field result.montgomeryValue?
    ]

/-- Header shared by the comparison runner's CSV-style output. -/
def reductionComparisonCsvHeader : String :=
  "name,modulus,a,b,preference,barrett,montgomery"

/--
Stable `Nat` extended-GCD benchmark cases.

The cases cover a small co-prime pair, two larger composites with
nontrivial gcd, and a power-of-two boundary-shaped input pair.
-/
def natExtGcdCases : List NatExtGcdCase :=
  [ { name := "nat-coprime-small", a := 123456789, b := 98765432 }
  , { name := "nat-composite-shared-factor", a := 60060 * 65537, b := 60060 * 32749 }
  , { name := "nat-power-of-two-boundary", a := 2 ^ 20 * 99991, b := 2 ^ 16 * 65535 }
  ]

/--
Stable `Int` extended-GCD benchmark cases.

These mirror the `Nat` workload shape while forcing sign handling in
the pure-Lean fallback and eventual GMP-backed path.
-/
def intExtGcdCases : List IntExtGcdCase :=
  [ { name := "int-mixed-sign-large", a := 12345678912345, b := -987654321234 }
  , { name := "int-both-negative", a := -60060 * 65537, b := -60060 * 32749 }
  , { name := "int-asymmetric-magnitudes", a := 2 ^ 40 + 12345, b := -(2 ^ 24 + 6789) }
  ]

/--
Stable `UInt64` extended-GCD benchmark cases.

The committed inputs stay in range while exercising small, mid-size,
and near-word-boundary workloads.
-/
def uint64ExtGcdCases : List UInt64ExtGcdCase :=
  [ { name := "u64-coprime-near-word", a := 18446744073709551557, b := 4294967291 }
  , { name := "u64-shared-factor", a := 4294967295 * 65537, b := 4294967295 * 257 }
  , { name := "u64-fibonacci-shaped", a := 2971215073, b := 1836311903 }
  ]

/--
Stable modular-exponentiation benchmark cases.

The cases cover a small prime modulus, the common Fermat prime
`65537`, and a large odd modulus that keeps the executable path busy.
-/
def powModCases : List PowModCase :=
  [ { name := "powmod-small-prime", a := 5, n := 12345, p := 65537 }
  , { name := "powmod-large-base", a := 98765432109876543210, n := 4096, p := 1000000007 }
  , { name := "powmod-fermat-boundary", a := 1844674407370955161, n := 8191, p := 4294967291 }
  ]

/--
Stable Barrett-versus-Montgomery comparison cases.

The committed cases cover a tiny Barrett-friendly modulus, one modulus
near the top of the current Barrett range, and one odd modulus that is
small enough for the current Montgomery scaffold and serves as the
committed Montgomery-favored crossover point.
-/
def reductionComparisonCases : List ReductionComparisonCase :=
  [ { id := .barrettTiny
    , name := "reduction-barrett-tiny"
    , modulus := 257
    , a := 231
    , b := 199
    , preference := .barrett
    }
  , { id := .barrettUpperEdge
    , name := "reduction-barrett-upper-edge"
    , modulus := 4294967291
    , a := 4294967289
    , b := 4294967231
    , preference := .crossover
    }
  , { id := .montgomeryCrossover
    , name := "reduction-montgomery-crossover"
    , modulus := 65537
    , a := 65535
    , b := 65521
    , preference := .montgomery
    }
  ]

/-- Execute one named `Nat` extended-GCD benchmark case. -/
def runNatExtGcdCase (c : NatExtGcdCase) : NatExtGcdResult :=
  let (g, s, t) := HexArith.extGcd c.a c.b
  { name := c.name, gcd := g, s := s, t := t }

/-- Execute one named `Int` extended-GCD benchmark case. -/
def runIntExtGcdCase (c : IntExtGcdCase) : IntExtGcdResult :=
  let (g, s, t) := HexArith.Int.extGcd c.a c.b
  { name := c.name, gcd := g, s := s, t := t }

/-- Execute one named `UInt64` extended-GCD benchmark case. -/
def runUInt64ExtGcdCase (c : UInt64ExtGcdCase) : UInt64ExtGcdResult :=
  let (g, s, t) := HexArith.UInt64.extGcd c.a c.b
  { name := c.name, gcd := g, s := s, t := t }

/-- Execute one named modular-exponentiation benchmark case. -/
def runPowModCase (c : PowModCase) : PowModResult :=
  { name := c.name, value := HexArith.powMod c.a c.n c.p }

/-- Execute the Barrett path for one committed comparison case. -/
def runBarrettComparison? (id : ReductionComparisonCaseId) : Option UInt64 :=
  match id with
  | .barrettTiny =>
      let ctx : BarrettCtx 257 := BarrettCtx.mk 257 (by decide) (by decide)
      some (ctx.mulMod 231 199)
  | .barrettUpperEdge =>
      let ctx : BarrettCtx 4294967291 := BarrettCtx.mk 4294967291 (by decide) (by decide)
      some (ctx.mulMod 4294967289 4294967231)
  | .montgomeryCrossover =>
      let ctx : BarrettCtx 65537 := BarrettCtx.mk 65537 (by decide) (by decide)
      some (ctx.mulMod 65535 65521)

/-- Execute the Montgomery path for one committed comparison case when supported. -/
def runMontgomeryComparison? (id : ReductionComparisonCaseId) : Option UInt64 :=
  match id with
  | .barrettTiny =>
      let ctx : MontCtx 257 := MontCtx.mk 257 (by decide)
      some (ctx.fromMont (ctx.mulMont (ctx.toMont 231) (ctx.toMont 199)))
  | .barrettUpperEdge =>
      none
  | .montgomeryCrossover =>
      let ctx : MontCtx 65537 := MontCtx.mk 65537 (by decide)
      some (ctx.fromMont (ctx.mulMont (ctx.toMont 65535) (ctx.toMont 65521)))

/-- Execute one named reduction-comparison benchmark case. -/
def runReductionComparisonCase (c : ReductionComparisonCase) : ReductionComparisonResult :=
  { name := c.name
  , modulus := c.modulus
  , a := c.a
  , b := c.b
  , preference := c.preference
  , barrettValue? := runBarrettComparison? c.id
  , montgomeryValue? := runMontgomeryComparison? c.id
  }

/-- Execute all committed `Nat` extended-GCD benchmark cases. -/
def runNatExtGcdCases : List NatExtGcdResult :=
  natExtGcdCases.map runNatExtGcdCase

/-- Execute all committed `Int` extended-GCD benchmark cases. -/
def runIntExtGcdCases : List IntExtGcdResult :=
  intExtGcdCases.map runIntExtGcdCase

/-- Execute all committed `UInt64` extended-GCD benchmark cases. -/
def runUInt64ExtGcdCases : List UInt64ExtGcdResult :=
  uint64ExtGcdCases.map runUInt64ExtGcdCase

/-- Execute all committed modular-exponentiation benchmark cases. -/
def runPowModCases : List PowModResult :=
  powModCases.map runPowModCase

/-- Execute all committed `Nat` extended-GCD cases and return CSV-style rows. -/
def runNatExtGcdCsv : List String :=
  natExtGcdCsvHeader :: runNatExtGcdCases.map NatExtGcdResult.toCsvRow

/-- Execute all committed `Int` extended-GCD cases and return CSV-style rows. -/
def runIntExtGcdCsv : List String :=
  intExtGcdCsvHeader :: runIntExtGcdCases.map IntExtGcdResult.toCsvRow

/-- Execute all committed `UInt64` extended-GCD cases and return CSV-style rows. -/
def runUInt64ExtGcdCsv : List String :=
  uint64ExtGcdCsvHeader :: runUInt64ExtGcdCases.map UInt64ExtGcdResult.toCsvRow

/-- Execute all committed modular-exponentiation cases and return CSV-style rows. -/
def runPowModCsv : List String :=
  powModCsvHeader :: runPowModCases.map PowModResult.toCsvRow

/-- Execute all committed reduction-comparison benchmark cases. -/
def runReductionComparisonCases : List ReductionComparisonResult :=
  reductionComparisonCases.map runReductionComparisonCase

/-- Execute all comparison cases and return CSV-style rows for tooling. -/
def runReductionComparisonCsv : List String :=
  reductionComparisonCsvHeader :: runReductionComparisonCases.map ReductionComparisonResult.toCsvRow

end HexArith.Benchmark
