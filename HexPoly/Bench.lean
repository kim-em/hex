import HexPoly
import LeanBench

/-!
Benchmark registrations for `hex-poly`.

This Phase 4 slice measures the dense core operations over deterministic
integer polynomials. Input construction is hoisted into `prep`, and each timed
target returns a small checksum or scalar observable rather than the full
polynomial.

Scientific registrations:

* `runAddChecksum`: dense coefficientwise addition, `O(n)`.
* `runSubChecksum`: dense coefficientwise subtraction, `O(n)`.
* `runMulChecksum`: schoolbook dense multiplication, `O(n^2)`.
* `runEval`: Horner evaluation, `O(n)`.
* `runComposeChecksum`: Horner composition using schoolbook multiplication,
  `O(n^3)` for same-size dense inputs.
* `runDerivativeChecksum`: formal derivative, `O(n)`.

Euclidean division, gcd/xgcd, integer content/primitive part, and polynomial
CRT are intentionally left for later Phase 4 slices.
-/

namespace Hex.PolyBench

/-- Hash prepared dense-polynomial inputs by their normalized coefficient arrays. -/
instance [Hashable R] [Zero R] [DecidableEq R] : Hashable (DensePoly R) where
  hash p := hash p.toArray

/-- Prepared input for binary dense-polynomial operations. -/
structure BinaryInput where
  lhs : DensePoly Int
  rhs : DensePoly Int
  deriving Hashable

/-- Prepared input for unary dense-polynomial operations. -/
structure UnaryInput where
  poly : DensePoly Int
  deriving Hashable

/-- Prepared input for Horner evaluation. -/
structure EvalInput where
  poly : DensePoly Int
  point : Int
  deriving Hashable

/-- Prepared input for polynomial composition. -/
structure ComposeInput where
  outer : DensePoly Int
  inner : DensePoly Int
  deriving Hashable

/-- Deterministic nonzero-ish coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 1009
  Int.ofNat (raw + 1)

/-- Deterministic dense polynomial with `n` generated coefficients. -/
def densePoly (n salt : Nat) : DensePoly Int :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => coeffValue n i salt

/-- Stable scalar observable for polynomial-valued benchmark results. -/
def checksum (p : DensePoly Int) : Int :=
  p.toArray.foldl (fun acc coeff => acc * 65_537 + coeff) 0

/-- Per-parameter fixture for addition, subtraction, and multiplication. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  { lhs := densePoly n 11
    rhs := densePoly n 37 }

/-- Per-parameter fixture for derivative benchmarks. -/
def prepUnaryInput (n : Nat) : UnaryInput :=
  { poly := densePoly n 53 }

/-- Per-parameter fixture for Horner evaluation. -/
def prepEvalInput (n : Nat) : EvalInput :=
  { poly := densePoly n 71
    point := 3 }

/-- Per-parameter fixture for same-size dense polynomial composition. -/
def prepComposeInput (n : Nat) : ComposeInput :=
  { outer := densePoly n 89
    inner := densePoly n 107 }

/-- Benchmark target: add two prepared dense polynomials and checksum the result. -/
def runAddChecksum (input : BinaryInput) : Int :=
  checksum (input.lhs + input.rhs)

/-- Benchmark target: subtract two prepared dense polynomials and checksum the result. -/
def runSubChecksum (input : BinaryInput) : Int :=
  checksum (input.lhs - input.rhs)

/-- Benchmark target: multiply two prepared dense polynomials and checksum the result. -/
def runMulChecksum (input : BinaryInput) : Int :=
  checksum (input.lhs * input.rhs)

/-- Benchmark target: evaluate a prepared dense polynomial at a fixed point. -/
def runEval (input : EvalInput) : Int :=
  DensePoly.eval input.poly input.point

/-- Benchmark target: compose two prepared same-size dense polynomials. -/
def runComposeChecksum (input : ComposeInput) : Int :=
  checksum (DensePoly.compose input.outer input.inner)

/-- Benchmark target: compute the formal derivative and checksum the result. -/
def runDerivativeChecksum (input : UnaryInput) : Int :=
  checksum (DensePoly.derivative input.poly)

setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

setup_benchmark runSubChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

setup_benchmark runMulChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

setup_benchmark runEval n => n
  with prep := prepEvalInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

setup_benchmark runComposeChecksum n => n * n * n
  with prep := prepComposeInput
  where {
    paramFloor := 16
    paramCeiling := 64
    paramSchedule := .custom #[16, 24, 32, 48, 64]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

setup_benchmark runDerivativeChecksum n => n
  with prep := prepUnaryInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

end Hex.PolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
