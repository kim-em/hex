import HexArith.ExtGcd
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

end HexArith.Benchmark
