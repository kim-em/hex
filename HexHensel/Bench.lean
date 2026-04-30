import HexHensel.Multifactor
import HexHensel.Quadratic
import LeanBench

/-!
Benchmark registrations for `hex-hensel`.

This Phase 4 infrastructure slice measures the executable bridge operations,
linear and quadratic Hensel lift steps, and the ordered multifactor helpers.
Inputs are deterministic and use the fixed small prime `5`; timed targets
return compact checksums of the computed polynomial data.

Scientific registrations:

* `runModPChecksum`: coefficient reduction from `Z[x]` to `F_5[x]`, `O(n)`.
* `runLiftToZChecksum`: canonical lift from `F_5[x]` to `Z[x]`, `O(n)`.
* `runReduceModPowChecksum`: coefficient reduction modulo `5^k`, `O(n)`.
* `runLinearHenselStepChecksum`: one linear Hensel correction, `O(n^2)`.
* `runHenselLiftChecksum`: fixed-precision iterative linear lift, `O(n^2)`.
* `runQuadraticHenselStepChecksum`: one quadratic Hensel correction, `O(n^2)`.
* `runPolyProductChecksum`: ordered product of `n` linear factors, `O(n^2)`.
* `runMultifactorLiftChecksum`: two-factor ordered multifactor lift, `O(n^2)`.
-/

namespace Hex
namespace HenselBench

private instance benchBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

instance : Hashable ZPoly where
  hash p := hash p.toArray

instance {p : Nat} [ZMod64.Bounds p] : Hashable (ZMod64 p) where
  hash a := hash a.toNat

instance {p : Nat} [ZMod64.Bounds p] : Hashable (FpPoly p) where
  hash f := hash f.toArray

/-- Prepared input for bridge benchmarks. -/
structure BridgeInput where
  zpoly : ZPoly
  fpoly : FpPoly 5
  deriving Hashable

/-- Prepared input for one linear Hensel step and the iterative wrapper. -/
structure LinearInput where
  f : ZPoly
  g : ZPoly
  h : ZPoly
  s : FpPoly 5
  t : FpPoly 5
  deriving Hashable

/-- Prepared input for one quadratic Hensel step. -/
structure QuadraticInput where
  f : ZPoly
  g : ZPoly
  h : ZPoly
  s : ZPoly
  t : ZPoly
  deriving Hashable

/-- Prepared input for ordered multifactor helpers. -/
structure MultifactorInput where
  f : ZPoly
  factors : Array ZPoly
  deriving Hashable

/-- Deterministic integer coefficient generator keyed by size, index, and salt. -/
def zCoeffValue (n i salt : Nat) : Int :=
  let raw := ((i + 3) * (salt + 19) + (i + 1) * (i + 5) * 11 + n * 37) % 997
  let value := Int.ofNat (raw + 1)
  if (i + salt) % 2 = 0 then value else -value

/-- Deterministic `F_5` coefficient generator keyed by size, index, and salt. -/
def fpCoeffValue (n i salt : Nat) : ZMod64 5 :=
  ZMod64.ofNat 5 <|
    ((i + 1) * (salt + 7) + (i + 5) * (i + 9) * 3 + n * 13) % 5

/-- Deterministic dense integer polynomial with `n` generated coefficients. -/
def denseZPoly (n salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| (Array.range n).map fun i => zCoeffValue n i salt

/-- Deterministic dense `F_5` polynomial with `n` generated coefficients. -/
def denseFpPoly (n salt : Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs <| (Array.range n).map fun i => fpCoeffValue n i salt

/-- Deterministic monic integer linear factor. -/
def linearZFactor (salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs #[Int.ofNat ((salt % 4) + 1), 1]

/-- Deterministic monic `F_5` linear factor. -/
def linearFpFactor (salt : Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs #[fpCoeffValue 1 0 salt, 1]

/-- Stable checksum for integer-polynomial benchmark results. -/
def checksumZPoly (f : ZPoly) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for finite-field-polynomial benchmark results. -/
def checksumFpPoly {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : UInt64 :=
  f.toArray.foldl (fun acc coeff => mixHash acc (hash coeff)) 0

/-- Stable checksum for an ordered array of integer polynomials. -/
def checksumZPolyArray (polys : Array ZPoly) : UInt64 :=
  polys.foldl (fun acc f => mixHash acc (checksumZPoly f)) 0

/-- Per-parameter fixture for bridge operations. -/
def prepBridgeInput (n : Nat) : BridgeInput :=
  { zpoly := denseZPoly n 17
    fpoly := denseFpPoly n 23 }

/-- Per-parameter fixture for linear Hensel operations.

The factor error is built as a multiple of `5`, so the correction path is
nontrivial while staying deterministic.
-/
def prepLinearInput (n : Nat) : LinearInput :=
  let g := linearZFactor 31
  let h := denseZPoly (n + 1) 37
  let e := denseZPoly (n + 1) 41
  let f := g * h + DensePoly.scale (5 : Int) e
  { f := f
    g := g
    h := h
    s := 0
    t := 1 }

/-- Per-parameter fixture for quadratic Hensel operations. -/
def prepQuadraticInput (n : Nat) : QuadraticInput :=
  let g := linearZFactor 43
  let h := denseZPoly (n + 1) 47
  let e := denseZPoly (n + 1) 53
  let f := g * h + DensePoly.scale (5 : Int) e
  { f := f
    g := g
    h := h
    s := 0
    t := 1 }

/-- Per-parameter fixture for the ordered product of many small factors. -/
def prepProductInput (n : Nat) : MultifactorInput :=
  let factors := (Array.range n).map linearZFactor
  { f := Array.polyProduct factors
    factors := factors }

/-- Per-parameter fixture for the two-factor multifactor lifting path. -/
def prepMultifactorLiftInput (n : Nat) : MultifactorInput :=
  let g := linearZFactor 59
  let h := denseZPoly (n + 1) 61
  let factors := #[g, h]
  let e := denseZPoly (n + 1) 67
  { f := Array.polyProduct factors + DensePoly.scale (5 : Int) e
    factors := factors }

/-- Benchmark target: reduce integer coefficients modulo `5`. -/
def runModPChecksum (input : BridgeInput) : UInt64 :=
  checksumFpPoly <| ZPoly.modP 5 input.zpoly

/-- Benchmark target: lift `F_5` coefficients to canonical integer representatives. -/
def runLiftToZChecksum (input : BridgeInput) : UInt64 :=
  checksumZPoly <| FpPoly.liftToZ input.fpoly

/-- Benchmark target: reduce integer coefficients modulo `5^3`. -/
def runReduceModPowChecksum (input : BridgeInput) : UInt64 :=
  checksumZPoly <| ZPoly.reduceModPow input.zpoly 5 3

/-- Benchmark target: one linear Hensel correction step. -/
def runLinearHenselStepChecksum (input : LinearInput) : UInt64 :=
  let r := ZPoly.linearHenselStep 5 1 input.f input.g input.h input.s input.t
  mixHash (checksumZPoly r.g) (checksumZPoly r.h)

/-- Benchmark target: fixed-precision iterative linear Hensel lift. -/
def runHenselLiftChecksum (input : LinearInput) : UInt64 :=
  let r := ZPoly.henselLift 5 4 input.f input.g input.h input.s input.t
  mixHash (checksumZPoly r.g) (checksumZPoly r.h)

/-- Benchmark target: one quadratic Hensel correction step. -/
def runQuadraticHenselStepChecksum (input : QuadraticInput) : UInt64 :=
  let r := ZPoly.quadraticHenselStep 5 input.f input.g input.h input.s input.t
  mixHash (mixHash (checksumZPoly r.g) (checksumZPoly r.h))
    (mixHash (checksumZPoly r.s) (checksumZPoly r.t))

/-- Benchmark target: ordered product of prepared integer-polynomial factors. -/
def runPolyProductChecksum (input : MultifactorInput) : UInt64 :=
  checksumZPoly <| Array.polyProduct input.factors

/-- Benchmark target: ordered multifactor lift of two prepared factors. -/
def runMultifactorLiftChecksum (input : MultifactorInput) : UInt64 :=
  checksumZPolyArray <| ZPoly.multifactorLift 5 3 input.f input.factors

setup_benchmark runModPChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runLiftToZChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runReduceModPowChecksum n => n
  with prep := prepBridgeInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The linear step performs dense arithmetic against degree-`n` inputs, including
a correction product whose operands both grow linearly with the fixture size.
-/
setup_benchmark runLinearHenselStepChecksum n => n * n
  with prep := prepLinearInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The wrapper performs a fixed number of linear steps for precision `5^4`, so the
asymptotic model is the same quadratic dense-polynomial correction cost.
-/
setup_benchmark runHenselLiftChecksum n => n * n
  with prep := prepLinearInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
The quadratic step performs dense factor and Bezout correction products over
degree-`n` fixtures while the requested modulus size is fixed.
-/
setup_benchmark runQuadraticHenselStepChecksum n => n * n
  with prep := prepQuadraticInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
Left-folding `n` linear factors grows the accumulator degree one step at a
time, giving a quadratic total number of coefficient operations.
-/
setup_benchmark runPolyProductChecksum n => n * n
  with prep := prepProductInput
  where {
    paramFloor := 128
    paramCeiling := 1024
    paramSchedule := .custom #[128, 192, 256, 384, 512, 768, 1024]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/-
This two-factor multifactor fixture exercises the public ordered lift helper;
with a fixed number of factors, the delegated Hensel lift dominates at
quadratic dense-polynomial cost.
-/
setup_benchmark runMultifactorLiftChecksum n => n * n
  with prep := prepMultifactorLiftInput
  where {
    paramFloor := 64
    paramCeiling := 512
    paramSchedule := .custom #[64, 96, 128, 192, 256, 384, 512]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end HenselBench
end Hex

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
