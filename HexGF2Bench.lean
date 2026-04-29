import HexGF2.Bench
import HexPolyFp

/-!
Executable-root additions for `hexgf2_bench`.

The library-owned `HexGF2/Bench.lean` module stays inside the `HexGF2`
dependency boundary. This executable root adds the cross-library `GF2Poly`
versus `FpPoly 2` comparison registrations named by the HexGF2 Phase 4 spec.
The comparison cases share deterministic input families and return
coefficient-domain checksums, so `lake exe hexgf2_bench compare ...` joins on a
real common domain.

Additional scientific registrations:

* `runPackedGcdCompareChecksum` and `runFp2GcdCompareChecksum`: packed
  `GF2Poly` versus generic `FpPoly 2` polynomial GCD on the same deterministic
  coefficient family, `O(n^2)`.
* `runPackedBerlekampCompareChecksum` and `runFp2BerlekampCompareChecksum`:
  packed versus generic Berlekamp-matrix-style Frobenius-column construction
  over the same monic modulus family, `O(n^3)`.
-/

namespace Hex.GF2Bench

private instance boundsTwo : ZMod64.Bounds 2 where
  pPos := by decide
  pLeR := by decide

instance {p : Nat} [ZMod64.Bounds p] : Hashable (ZMod64 p) where
  hash a := hash a.toNat

instance [Hashable R] [Zero R] [DecidableEq R] : Hashable (DensePoly R) where
  hash p := hash p.toArray

private abbrev F2Poly := FpPoly 2

/-- Prepared shared-domain packed/generic comparison input. -/
structure CompareInput where
  packedLhs : GF2Poly
  packedRhs : GF2Poly
  genericLhs : F2Poly
  genericRhs : F2Poly
  deriving Hashable

/-- Prepared shared-domain Berlekamp-matrix-style comparison input. -/
structure BerlekampCompareInput where
  packedModulus : GF2Poly
  genericModulus : F2Poly
  columnCount : Nat
  deriving Hashable

/-- Stable checksum for a packed polynomial in coefficient order. -/
def checksumPackedCoeffs (p : GF2Poly) : UInt64 :=
  match p.degree? with
  | none => 0
  | some d =>
      (Array.range (d + 1)).foldl
        (fun acc i => mixWord acc (if p.coeff i then 1 else 0))
        0

/-- Stable checksum for an `FpPoly 2` in coefficient order. -/
def checksumFp2Coeffs (p : F2Poly) : UInt64 :=
  p.toArray.foldl (fun acc c => mixWord acc (UInt64.ofNat c.toNat)) 0

/-- Coefficient bit used by shared packed/generic comparison fixtures. -/
def coeffBit (i salt : Nat) : Bool :=
  ((i + 1) * 9_176 + (salt + 3) * 1_021 + i * i * 17) % 5 < 2

/-- Shared-domain packed polynomial with a forced high coefficient. -/
def packedCoeffPoly (degree salt : Nat) : GF2Poly :=
  GF2Poly.ofWords <|
    Id.run do
      let wordCount := degree / 64 + 1
      let mut words := Array.replicate wordCount (0 : UInt64)
      for i in [0:degree + 1] do
        if coeffBit i salt || i = degree then
          let wordIdx := i / 64
          let bitIdx := i % 64
          words := words.set! wordIdx (words[wordIdx]! ||| ((1 : UInt64) <<< bitIdx.toUInt64))
      return words

/-- Shared-domain generic `FpPoly 2` with a forced high coefficient. -/
def fp2CoeffPoly (degree salt : Nat) : F2Poly :=
  FpPoly.ofCoeffs <|
    (Array.range (degree + 1)).map fun i =>
      if coeffBit i salt || i = degree then
        ZMod64.ofNat 2 1
      else
        ZMod64.ofNat 2 0

/-- Packed polynomial exponentiation modulo a nonzero modulus. -/
def packedPowMod (base modulus : GF2Poly) : Nat → GF2Poly → GF2Poly → GF2Poly
  | 0, _, acc => acc
  | k + 1, b, acc =>
      let acc' := if (k + 1) % 2 = 0 then acc else (acc * b) % modulus
      let b' := (b * b) % modulus
      packedPowMod base modulus ((k + 1) / 2) b' acc'
termination_by k _ _ => k
decreasing_by
  simpa using Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)

/-- Generic `FpPoly 2` exponentiation modulo a nonzero modulus. -/
def fp2PowMod (base modulus : F2Poly) : Nat → F2Poly → F2Poly → F2Poly
  | 0, _, acc => acc
  | k + 1, b, acc =>
      let acc' := if (k + 1) % 2 = 0 then acc else (acc * b) % modulus
      let b' := (b * b) % modulus
      fp2PowMod base modulus ((k + 1) / 2) b' acc'
termination_by k _ _ => k
decreasing_by
  simpa using Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)

/-- Per-parameter fixture for packed/generic polynomial GCD comparisons. -/
def prepCompareInput (n : Nat) : CompareInput :=
  let degree := 64 * n + 31
  { packedLhs := packedCoeffPoly degree 541
    packedRhs := packedCoeffPoly degree 577
    genericLhs := fp2CoeffPoly degree 541
    genericRhs := fp2CoeffPoly degree 577 }

/-- Per-parameter fixture for packed/generic Berlekamp-style comparisons. -/
def prepBerlekampCompareInput (n : Nat) : BerlekampCompareInput :=
  let degree := n + 2
  { packedModulus := packedCoeffPoly degree 613
    genericModulus := fp2CoeffPoly degree 613
    columnCount := degree }

/-- Benchmark target: packed polynomial GCD over a shared comparison family. -/
def runPackedGcdCompareChecksum (input : CompareInput) : UInt64 :=
  checksumPackedCoeffs (GF2Poly.gcd input.packedLhs input.packedRhs)

/-- Benchmark target: generic `FpPoly 2` GCD over the shared comparison family. -/
def runFp2GcdCompareChecksum (input : CompareInput) : UInt64 :=
  checksumFp2Coeffs (DensePoly.gcd input.genericLhs input.genericRhs)

/-- Benchmark target: packed Berlekamp-style Frobenius-column construction. -/
def runPackedBerlekampCompareChecksum (input : BerlekampCompareInput) : UInt64 :=
  (Array.range input.columnCount).foldl
    (fun acc j =>
      let col := packedPowMod (GF2Poly.monomial 1) input.packedModulus (2 * j)
        ((GF2Poly.monomial 1) % input.packedModulus) 1
      mixWord acc (checksumPackedCoeffs col))
    0

/-- Benchmark target: generic `FpPoly 2` Berlekamp-style Frobenius-column construction. -/
def runFp2BerlekampCompareChecksum (input : BerlekampCompareInput) : UInt64 :=
  (Array.range input.columnCount).foldl
    (fun acc j =>
      let col := fp2PowMod (FpPoly.X : F2Poly) input.genericModulus (2 * j)
        ((FpPoly.X : F2Poly) % input.genericModulus) (1 : F2Poly)
      mixWord acc (checksumFp2Coeffs col))
    0

setup_benchmark runPackedGcdCompareChecksum n => n * n
  with prep := prepCompareInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runFp2GcdCompareChecksum n => n * n
  with prep := prepCompareInput
  where {
    paramFloor := 16
    paramCeiling := 128
    paramSchedule := .custom #[16, 24, 32, 48, 64, 96, 128]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runPackedBerlekampCompareChecksum n => n * n * n
  with prep := prepBerlekampCompareInput
  where {
    paramFloor := 8
    paramCeiling := 64
    paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runFp2BerlekampCompareChecksum n => n * n * n
  with prep := prepBerlekampCompareInput
  where {
    paramFloor := 8
    paramCeiling := 64
    paramSchedule := .custom #[8, 12, 16, 24, 32, 48, 64]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.GF2Bench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
