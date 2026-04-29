import HexGF2
import LeanBench

/-!
Benchmark registrations for `hex-gf2`.

This Phase 4 packed-core slice measures deterministic `GF2Poly` word-level
operations. Input construction is hoisted into `prep`, and polynomial-valued
targets return compact checksums over normalized packed words.

Scientific registrations:

* `runPureClmulChecksum`: pure Lean carry-less word multiplication, `O(n)`.
* `runClmulChecksum`: extern-backed carry-less word multiplication, `O(n)`.
* `runAddChecksum`: packed polynomial XOR addition, `O(n)`.
* `runMulChecksum`: packed schoolbook carry-less multiplication, `O(n^2)`.
* `runShiftLeftChecksum`: packed left shift by a size-proportional amount,
  `O(n)`.
* `runShiftRightChecksum`: packed right shift by a size-proportional amount,
  `O(n)`.
* `runDivChecksum`: packed long-division quotient extraction, `O(n^2)`.
* `runModChecksum`: packed long-division remainder extraction, `O(n^2)`.
* `runGcdChecksum`: packed Euclidean gcd, `O(n^2)` on deterministic
  same-size fixtures.
* `runXGcdChecksum`: packed extended Euclidean algorithm, `O(n^2)` on
  deterministic same-size fixtures.
-/

namespace Hex.GF2Bench

/-- Hash packed polynomials by their normalized word arrays in benchmark inputs. -/
instance : Hashable GF2Poly where
  hash p := hash p.toWords

/-- One prepared carry-less word-multiply sample. -/
structure WordSample where
  lhs : UInt64
  rhs : UInt64
  deriving Hashable

/-- Prepared word samples for `pureClmul` and extern `clmul`. -/
structure WordInput where
  samples : Array WordSample
  deriving Hashable

/-- Prepared binary polynomial-operation input. -/
structure BinaryInput where
  lhs : GF2Poly
  rhs : GF2Poly
  deriving Hashable

/-- Prepared polynomial plus a shift amount. -/
structure ShiftInput where
  poly : GF2Poly
  shift : Nat
  deriving Hashable

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Stable checksum for one carry-less 128-bit product. -/
def checksumClmulPair (acc : UInt64) (pair : UInt64 × UInt64) : UInt64 :=
  mixWord (mixWord acc pair.1) pair.2

/-- Stable checksum for a packed polynomial's normalized words. -/
def checksumPoly (p : GF2Poly) : UInt64 :=
  p.toWords.foldl mixWord 0

/-- Stable checksum for two packed polynomial outputs. -/
def checksumPolyPair (p q : GF2Poly) : UInt64 :=
  mixWord (checksumPoly p) (checksumPoly q)

/-- Deterministic nonzero-ish packed word generator keyed by index and salt. -/
def wordValue (i salt : Nat) : UInt64 :=
  UInt64.ofNat <|
    ((i + 1) * 1_103_515_245 +
      (i + 17) * 12_345 +
      (salt + 97) * 65_537 +
      i * i * 31) % 18_446_744_073_709_551_557

/-- Deterministic normalized packed polynomial with `n` machine words. -/
def packedPoly (n salt : Nat) : GF2Poly :=
  if n = 0 then
    0
  else
    let words :=
      (Array.range n).map fun i =>
        let w := wordValue i salt
        if i + 1 = n then w ||| 1 else w
    GF2Poly.ofWords words

/-- Per-parameter fixture for word carry-less multiplication. -/
def prepWordInput (n : Nat) : WordInput :=
  { samples := (Array.range n).map fun i =>
      { lhs := wordValue i 11
        rhs := wordValue i 37 } }

/-- Per-parameter fixture for same-size binary polynomial operations. -/
def prepBinaryInput (n : Nat) : BinaryInput :=
  { lhs := packedPoly n 53
    rhs := packedPoly n 89 }

/-- Per-parameter fixture for division-style operations. -/
def prepDivInput (n : Nat) : BinaryInput :=
  { lhs := packedPoly (2 * n + 1) 131
    rhs := packedPoly (n + 1) 173 }

/-- Per-parameter fixture for same-size Euclidean operations. -/
def prepGcdInput (n : Nat) : BinaryInput :=
  { lhs := packedPoly (n + 1) 197
    rhs := packedPoly (n + 1) 229 }

/-- Per-parameter fixture for left shifts by a size-proportional amount. -/
def prepShiftLeftInput (n : Nat) : ShiftInput :=
  { poly := packedPoly n 251
    shift := 32 * n + 13 }

/-- Per-parameter fixture for right shifts by a size-proportional amount. -/
def prepShiftRightInput (n : Nat) : ShiftInput :=
  { poly := packedPoly (2 * n + 1) 283
    shift := 32 * n + 13 }

/-- Benchmark target: pure Lean carry-less word multiplication. -/
def runPureClmulChecksum (input : WordInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => checksumClmulPair acc (pureClmul sample.lhs sample.rhs))
    0

/-- Benchmark target: extern-backed carry-less word multiplication. -/
def runClmulChecksum (input : WordInput) : UInt64 :=
  input.samples.foldl
    (fun acc sample => checksumClmulPair acc (clmul sample.lhs sample.rhs))
    0

/-- Benchmark target: add two prepared packed polynomials and checksum the result. -/
def runAddChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (input.lhs + input.rhs)

/-- Benchmark target: multiply two prepared packed polynomials and checksum the result. -/
def runMulChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (input.lhs * input.rhs)

/-- Benchmark target: shift a prepared packed polynomial left. -/
def runShiftLeftChecksum (input : ShiftInput) : UInt64 :=
  checksumPoly (input.poly.shiftLeft input.shift)

/-- Benchmark target: shift a prepared packed polynomial right. -/
def runShiftRightChecksum (input : ShiftInput) : UInt64 :=
  checksumPoly (input.poly.shiftRight input.shift)

/-- Benchmark target: compute the quotient from packed long division. -/
def runDivChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (input.lhs / input.rhs)

/-- Benchmark target: compute the remainder from packed long division. -/
def runModChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (input.lhs % input.rhs)

/-- Benchmark target: compute packed polynomial gcd. -/
def runGcdChecksum (input : BinaryInput) : UInt64 :=
  checksumPoly (GF2Poly.gcd input.lhs input.rhs)

/-- Benchmark target: compute packed extended gcd and checksum all outputs. -/
def runXGcdChecksum (input : BinaryInput) : UInt64 :=
  let result := GF2Poly.xgcd input.lhs input.rhs
  mixWord (checksumPoly result.gcd) (checksumPolyPair result.left result.right)

setup_benchmark runPureClmulChecksum n => n
  with prep := prepWordInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runClmulChecksum n => n
  with prep := prepWordInput
  where {
    paramFloor := 65536
    paramCeiling := 1048576
    paramSchedule := .custom #[65536, 131072, 262144, 524288, 1048576]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runAddChecksum n => n
  with prep := prepBinaryInput
  where {
    paramFloor := 4096
    paramCeiling := 65536
    paramSchedule := .custom #[4096, 8192, 16384, 32768, 65536]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runMulChecksum n => n * n
  with prep := prepBinaryInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runShiftLeftChecksum n => n
  with prep := prepShiftLeftInput
  where {
    paramFloor := 4096
    paramCeiling := 65536
    paramSchedule := .custom #[4096, 8192, 16384, 32768, 65536]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runShiftRightChecksum n => n
  with prep := prepShiftRightInput
  where {
    paramFloor := 4096
    paramCeiling := 65536
    paramSchedule := .custom #[4096, 8192, 16384, 32768, 65536]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runDivChecksum n => n * n
  with prep := prepDivInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runModChecksum n => n * n
  with prep := prepDivInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runGcdChecksum n => n * n
  with prep := prepGcdInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runXGcdChecksum n => n * n
  with prep := prepGcdInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.GF2Bench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
