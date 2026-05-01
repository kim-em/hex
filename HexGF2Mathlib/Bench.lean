import HexGF2Mathlib.Basic
import LeanBench

/-!
Benchmark registrations for the `HexGF2Mathlib` packed-polynomial bridge.

This Phase 4 slice measures the conversion surfaces that connect the packed
`Hex.GF2Poly` execution path to the generic `Hex.FpPoly 2` representation.
The lower-level packed arithmetic benchmarks remain in `HexGF2.Bench`; this
module focuses on bridge conversion cost.

Scientific registrations:

* `runToFpPolyChecksum`: unpack packed words into dense `FpPoly 2`
  coefficients, `O(n)` in generated words/coefficients.
* `runOfFpPolyChecksum`: repack dense `FpPoly 2` coefficients into words,
  `O(n)` in generated words/coefficients.
* `runRoundTripChecksum`: perform both packed and dense conversion round trips
  over bounded-degree generated inputs, `O(n)`.
-/

namespace HexGF2Mathlib.GF2Bench

open Hex
open HexGF2Mathlib

instance : Hashable (ZMod64 2) where
  hash a := hash a.toNat

instance : Hashable (FpPoly 2) where
  hash f := hash f.toArray

instance : Hashable GF2Poly where
  hash p := hash p.toWords

/-- Prepared packed bridge input with degree bounded by the generated words. -/
structure PackedInput where
  poly : GF2Poly
  deriving Hashable

/-- Prepared dense bridge input with coefficients bounded by the generated words. -/
structure DenseInput where
  poly : FpPoly 2
  deriving Hashable

/-- Prepared paired packed and dense bridge inputs for round-trip checksums. -/
structure RoundTripInput where
  packed : GF2Poly
  dense : FpPoly 2
  deriving Hashable

/-- Deterministic mixing over machine words for compact benchmark observables. -/
def mixWord (acc x : UInt64) : UInt64 :=
  acc * 0x9E3779B97F4A7C15 + x + 0xBF58476D1CE4E5B9

/-- Stable checksum for a packed polynomial's normalized words. -/
def checksumPacked (p : GF2Poly) : UInt64 :=
  p.toWords.foldl mixWord 0

/-- Stable checksum for a dense `FpPoly 2` coefficient array. -/
def checksumDense (p : FpPoly 2) : UInt64 :=
  p.toArray.foldl (fun acc coeff => mixWord acc (UInt64.ofNat coeff.toNat)) 0

/-- Deterministic nonzero packed word generator keyed by index and salt. -/
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

/-- Deterministic `F_2` coefficient generator keyed by size, index, and salt. -/
def coeffValueTwo (n i salt : Nat) : ZMod64 2 :=
  ZMod64.ofNat 2 <|
    ((i + 1) * (salt + 17) + (i + 3) * (i + 5) * 13 + n * 29) % 2

/-- Deterministic dense `FpPoly 2` with `64 * n` generated coefficients. -/
def densePolyTwoWords (n salt : Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs <| (Array.range (64 * n)).map fun i => coeffValueTwo n i salt

/-- Per-parameter packed fixture for unpacking to the dense representation. -/
def prepPackedInput (n : Nat) : PackedInput :=
  { poly := packedPoly n 53 }

/-- Per-parameter dense fixture for repacking into the packed representation. -/
def prepDenseInput (n : Nat) : DenseInput :=
  { poly := densePolyTwoWords n 89 }

/-- Per-parameter paired fixture for both conversion round trips. -/
def prepRoundTripInput (n : Nat) : RoundTripInput :=
  { packed := packedPoly n 131
    dense := densePolyTwoWords n 173 }

/-- Benchmark target: unpack one packed polynomial and checksum dense coefficients. -/
def runToFpPolyChecksum (input : PackedInput) : UInt64 :=
  checksumDense (GF2Poly.toFpPoly input.poly)

/-- Benchmark target: repack one dense `FpPoly 2` and checksum packed words. -/
def runOfFpPolyChecksum (input : DenseInput) : UInt64 :=
  checksumPacked (GF2Poly.ofFpPoly input.poly)

/-- Benchmark target: checksum both packed and dense conversion round trips. -/
def runRoundTripChecksum (input : RoundTripInput) : UInt64 :=
  let packedRoundTrip := GF2Poly.ofFpPoly (GF2Poly.toFpPoly input.packed)
  let denseRoundTrip := GF2Poly.toFpPoly (GF2Poly.ofFpPoly input.dense)
  mixWord (checksumPacked packedRoundTrip) (checksumDense denseRoundTrip)

/- Cost model: `GF2Poly.toFpPoly` enumerates each coefficient up to the packed
degree and builds a dense coefficient array. With `n` generated machine words,
that is `64 * n` coefficient visits, so the textbook model is linear in `n`. -/
setup_benchmark runToFpPolyChecksum n => n
  with prep := prepPackedInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: `GF2Poly.ofFpPoly` scans one 64-coefficient chunk for each
output word. The fixture has `64 * n` generated coefficients, so it performs
linear work in the generated coefficient/word count. -/
setup_benchmark runOfFpPolyChecksum n => n
  with prep := prepDenseInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the round-trip target performs one packed-to-dense conversion
and one dense-to-packed conversion over bounded-degree inputs of the same
generated size. Both passes are linear, so their composition remains `O(n)`. -/
setup_benchmark runRoundTripChecksum n => n
  with prep := prepRoundTripInput
  where {
    paramFloor := 1024
    paramCeiling := 16384
    paramSchedule := .custom #[1024, 2048, 4096, 8192, 16384]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end HexGF2Mathlib.GF2Bench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
