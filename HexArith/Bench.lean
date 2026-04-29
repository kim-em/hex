import HexArith
import LeanBench

/-!
Benchmark registrations for `hex-arith`.

This Phase 4 slice compares two implementations of the same repeated modular
multiplication task over the shared small odd modulus `65537`: Barrett reduction
for one-off modular products, and Montgomery arithmetic with factors converted
to Montgomery form in the prepared input.

Scientific registrations:

* `runBarrettMulChain`: repeated modular multiplication with `BarrettCtx.mulMod`,
  `O(n)`.
* `runMontgomeryMulChain`: the same multiplication chain using
  `MontCtx.toMont`, `MontCtx.mulMont`, and `MontCtx.fromMont`, `O(n)`.
-/

namespace Hex.ArithBench

/-- Shared small odd modulus in the overlap between Barrett and Montgomery. -/
def benchModulus : UInt64 :=
  65_537

/-- Barrett context for the shared benchmark modulus. -/
def barrettCtx : BarrettCtx benchModulus :=
  BarrettCtx.mk benchModulus (by decide) (by decide)

/-- Montgomery context for the shared benchmark modulus. -/
def montCtx : MontCtx benchModulus :=
  MontCtx.mk benchModulus (by decide)

/-- Prepared inputs for repeated modular multiplication. -/
structure MulChainInput where
  factors : Array UInt64
  montFactors : Array UInt64
  deriving Repr, BEq, Hashable

/-- Deterministic residue generator, always returning `0 < x < benchModulus`. -/
def factorAt (i : Nat) : UInt64 :=
  let x :=
    ((i + 1) * 1_103_515_245 +
      (i + 17) * 12_345 +
      0x9E37) % 65_536
  UInt64.ofNat (x + 1)

/-- Deterministic input family shared by both benchmark registrations. -/
def prepMulChainInput (n : Nat) : MulChainInput :=
  let factors := (Array.range n).map factorAt
  { factors := factors
    montFactors := factors.map montCtx.toMont }

/-- Run the chain directly in standard representation with Barrett reduction. -/
def runBarrettMulChain (input : MulChainInput) : UInt64 :=
  input.factors.foldl (fun acc x => barrettCtx.mulMod acc x) 1

/--
Run the same chain through Montgomery representation. Factor conversion is
hoisted into `prepMulChainInput`; the timed operation is the hot multiplication
loop plus the final conversion out of Montgomery form.
-/
def runMontgomeryMulChain (input : MulChainInput) : UInt64 :=
  let acc0 := montCtx.toMont 1
  let acc := input.montFactors.foldl
    (fun acc x => montCtx.mulMont acc x)
    acc0
  montCtx.fromMont acc

setup_benchmark runBarrettMulChain n => n
  with prep := prepMulChainInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

setup_benchmark runMontgomeryMulChain n => n
  with prep := prepMulChainInput
  where {
    paramFloor := 8192
    paramCeiling := 131072
    paramSchedule := .custom #[8192, 16384, 32768, 65536, 131072]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

end Hex.ArithBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
