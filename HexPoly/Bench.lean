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
* `runDivModChecksum`: field-polynomial long division returning quotient and
  remainder, `O(n^2)`.
* `runDivChecksum`: quotient extraction from field-polynomial long division,
  `O(n^2)`.
* `runModChecksum`: remainder extraction from field-polynomial long division,
  `O(n^2)`.
* `runModByMonicChecksum`: remainder from division by a monic divisor,
  `O(n^2)`.
* `runGcdChecksum`: Euclidean gcd over a field, `O(n^3)` with the current
  schoolbook division path.
* `runXGcdChecksum`: extended Euclidean algorithm over a field, `O(n^3)` with
  the current schoolbook division path.
* `runContent`: integer coefficient content, `O(n)`.
* `runPrimitivePartChecksum`: integer primitive part, `O(n)`.
* `runPolyCRTChecksum`: polynomial CRT witness construction over coprime
  monic moduli, `O(n^2)` with the current schoolbook multiplication path.
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

/-- Prepared input for integer content and primitive-part operations. -/
structure ContentInput where
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

/-- Prepared input for field-polynomial Euclidean operations. -/
structure EuclidInput where
  dividend : DensePoly Rat
  divisor : DensePoly Rat
  deriving Hashable

/-- Prepared input for division by a generated monic polynomial. -/
structure MonicInput where
  dividend : DensePoly Rat
  divisorDegree : Nat
  deriving Hashable

/-- Prepared input for polynomial CRT witness construction. -/
structure PolyCRTInput where
  modulusA : DensePoly Rat
  modulusB : DensePoly Rat
  residueA : DensePoly Rat
  residueB : DensePoly Rat
  bezoutS : DensePoly Rat
  bezoutT : DensePoly Rat
  deriving Hashable

/-- Deterministic nonzero-ish coefficient generator keyed by size, index, and salt. -/
def coeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 1009
  Int.ofNat (raw + 1)

/-- Deterministic dense polynomial with `n` generated coefficients. -/
def densePoly (n salt : Nat) : DensePoly Int :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => coeffValue n i salt

/-- Deterministic dense polynomial over `Rat` for field-operation benchmarks. -/
def denseRatPoly (n salt : Nat) : DensePoly Rat :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => (coeffValue n i salt : Rat)

/-- Deterministic primitive coefficient used inside nontrivial-content inputs. -/
def primitiveCoeffValue (n i salt : Nat) : Int :=
  let base : Int := if i = 0 then 1 else coeffValue n i salt
  if i % 2 = 0 then base else -base

/-- Deterministic integer polynomial whose coefficient content is nontrivial. -/
def contentPoly (n salt : Nat) : DensePoly Int :=
  let common : Int := Int.ofNat ((salt % 5) + 2)
  DensePoly.ofCoeffs <|
    (Array.range n).map fun i => common * primitiveCoeffValue n i salt

/-- Deterministic monic divisor used by `modByMonic` benchmarks. -/
def monicDivisor (degree : Nat) : DensePoly Rat :=
  { coeffs := (Array.replicate degree (0 : Rat)).push 1
    normalized := by
      right
      have hone : ¬((1 : Rat) = Zero.zero) := by decide
      simp [hone] }

/-- Generated monomial divisors are monic by construction. -/
theorem monicDivisor_monic (degree : Nat) : DensePoly.Monic (monicDivisor degree) := by
  simp [monicDivisor, DensePoly.Monic, DensePoly.leadingCoeff]

/-- Stable scalar observable for polynomial-valued benchmark results. -/
def checksum (p : DensePoly Int) : Int :=
  p.toArray.foldl (fun acc coeff => acc * 65_537 + coeff) 0

/-- Stable scalar observable for field-polynomial benchmark results. -/
def ratChecksum (p : DensePoly Rat) : Rat :=
  p.toArray.foldl (fun acc coeff => acc * 65_537 + coeff) 0

/-- Per-parameter fixture for addition, subtraction, and multiplication. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  { lhs := densePoly n 11
    rhs := densePoly n 37 }

/-- Per-parameter fixture for derivative benchmarks. -/
def prepUnaryInput (n : Nat) : UnaryInput :=
  { poly := densePoly n 53 }

/-- Per-parameter fixture for integer content and primitive-part benchmarks. -/
def prepContentInput (n : Nat) : ContentInput :=
  { poly := contentPoly n 229 }

/-- Per-parameter fixture for Horner evaluation. -/
def prepEvalInput (n : Nat) : EvalInput :=
  { poly := densePoly n 71
    point := 3 }

/-- Per-parameter fixture for same-size dense polynomial composition. -/
def prepComposeInput (n : Nat) : ComposeInput :=
  { outer := densePoly n 89
    inner := densePoly n 107 }

/-- Per-parameter fixture for field-polynomial long division. -/
def prepEuclidInput (n : Nat) : EuclidInput :=
  { dividend := denseRatPoly (2 * n + 1) 131
    divisor := denseRatPoly (n + 1) 173 }

/-- Per-parameter fixture for division by a monic polynomial. -/
def prepMonicInput (n : Nat) : MonicInput :=
  { dividend := denseRatPoly (2 * n + 1) 191
    divisorDegree := n + 1 }

/-- Per-parameter fixture for polynomial CRT witness construction. -/
def prepPolyCRTInput (n : Nat) : PolyCRTInput :=
  let modulusDegree := n + 1
  let monomial := DensePoly.monomial modulusDegree (1 : Rat)
  { modulusA := monomial
    modulusB := monomial + DensePoly.C (1 : Rat)
    residueA := denseRatPoly n 251
    residueB := denseRatPoly n 283
    bezoutS := DensePoly.C (-1 : Rat)
    bezoutT := DensePoly.C (1 : Rat) }

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

/-- Benchmark target: compute quotient and remainder, then checksum both outputs. -/
def runDivModChecksum (input : EuclidInput) : Rat :=
  let qr := DensePoly.divMod input.dividend input.divisor
  ratChecksum qr.1 * 131_071 + ratChecksum qr.2

/-- Benchmark target: compute the quotient from field-polynomial long division. -/
def runDivChecksum (input : EuclidInput) : Rat :=
  ratChecksum (input.dividend / input.divisor)

/-- Benchmark target: compute the remainder from field-polynomial long division. -/
def runModChecksum (input : EuclidInput) : Rat :=
  ratChecksum (input.dividend % input.divisor)

/-- Benchmark target: compute the remainder from division by a monic polynomial. -/
def runModByMonicChecksum (input : MonicInput) : Rat :=
  let divisor := monicDivisor input.divisorDegree
  ratChecksum (DensePoly.modByMonic input.dividend divisor (monicDivisor_monic input.divisorDegree))

/-- Benchmark target: compute the Euclidean gcd and checksum the result. -/
def runGcdChecksum (input : EuclidInput) : Rat :=
  ratChecksum (DensePoly.gcd input.dividend input.divisor)

/-- Benchmark target: compute extended gcd and checksum gcd plus Bezout outputs. -/
def runXGcdChecksum (input : EuclidInput) : Rat :=
  let result := DensePoly.xgcd input.dividend input.divisor
  ratChecksum result.gcd * 1_048_573 + ratChecksum result.left * 1_024 + ratChecksum result.right

/-- Benchmark target: compute integer coefficient content. -/
def runContent (input : ContentInput) : Int :=
  DensePoly.content input.poly

/-- Benchmark target: compute integer primitive part and checksum the result. -/
def runPrimitivePartChecksum (input : ContentInput) : Int :=
  checksum (DensePoly.primitivePart input.poly)

/-- Benchmark target: construct a polynomial CRT witness and checksum it. -/
def runPolyCRTChecksum (input : PolyCRTInput) : Rat :=
  ratChecksum <|
    DensePoly.polyCRT
      input.modulusA input.modulusB input.residueA input.residueB input.bezoutS input.bezoutT

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

setup_benchmark runDivModChecksum n => n * n
  with prep := prepEuclidInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

setup_benchmark runDivChecksum n => n * n
  with prep := prepEuclidInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

setup_benchmark runModChecksum n => n * n
  with prep := prepEuclidInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

setup_benchmark runModByMonicChecksum n => n * n
  with prep := prepMonicInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

setup_benchmark runGcdChecksum n => n * n * n
  with prep := prepEuclidInput
  where {
    paramFloor := 16
    paramCeiling := 96
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
  }

setup_benchmark runXGcdChecksum n => n * n * n
  with prep := prepEuclidInput
  where {
    paramFloor := 16
    paramCeiling := 96
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
  }

setup_benchmark runContent n => n
  with prep := prepContentInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

setup_benchmark runPrimitivePartChecksum n => n
  with prep := prepContentInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

setup_benchmark runPolyCRTChecksum n => n * n
  with prep := prepPolyCRTInput
  where {
    paramFloor := 128
    paramCeiling := 512
    paramSchedule := .custom #[128, 192, 256, 384, 512]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

end Hex.PolyBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
