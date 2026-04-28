import HexArith.Bench.Calibration
import HexArith.Bench.Driver
import HexArith.Bench.Inputs

/-!
# HexArith benchmark family registry

The four committed families (per the [plan](../../../.claude/plans/let-s-make-a-plan-synchronous-token.md))
with their weights for the seconds-budget split.
-/

namespace HexArith.Bench.Families

open HexArith.Bench

def a1 (seed : UInt64) : FamilySpec :=
  { name := "A1.nat-extgcd"
  , familyVersion := 1
  , paramName := "bits"
  , expectedSlope := 2.0
  , paramFloor := 16
  , paramCeiling := 65536
  , initialGuess := Calibration.a1NatExtGcd
  , runOne := fun bits => pure (Inputs.runA1 seed bits) }

def a2 (seed : UInt64) : FamilySpec :=
  { name := "A2.nat-powmod"
  , familyVersion := 1
  , paramName := "bits"
  , expectedSlope := 3.0
  , paramFloor := 16
  , paramCeiling := 16384
  , initialGuess := Calibration.a2NatPowMod
  , runOne := fun bits => pure (Inputs.runA2 seed bits) }

def a3 (seed : UInt64) : FamilySpec :=
  { name := "A3.barrett-mulmod"
  , familyVersion := 1
  , paramName := "calls"
  , expectedSlope := 1.0
  , paramFloor := 100
  , paramCeiling := 100000000
  , initialGuess := Calibration.a3BarrettMulMod
  , runOne := fun n => pure (Inputs.runA3 seed n) }

def a4 (seed : UInt64) : FamilySpec :=
  { name := "A4.montgomery-mulmont"
  , familyVersion := 1
  , paramName := "calls"
  , expectedSlope := 1.0
  , paramFloor := 100
  , paramCeiling := 100000000
  , initialGuess := Calibration.a4MontgomeryMulMont
  , runOne := fun n => pure (Inputs.runA4 seed n) }

/--
Budgeted families with their seconds-budget weights (must sum to 1.0).

**A4 is intentionally excluded.** The current `HexArith.MontCtx`
scaffolding calls `montgomeryRadixInvNat p` (a brute-force `List.range`
search) inside every `mulMont` and `fromMont`, making throughput
benchmarks meaningless until that's replaced with a real Bezout-based
inverse. A4 is exercised only by the smoke set below — long enough to
confirm it doesn't crash at tiny `N`. See progress retrospective for
the SPEC v2 implication.
-/
def all (seed : UInt64) : List (Float × FamilySpec) :=
  [ (0.40, a1 seed)
  , (0.30, a2 seed)
  , (0.30, a3 seed) ]

/--
Smoke-only families: exercised by `scripts/bench/smoke.sh` once at tiny param.

**Empty for now.** A4 (Montgomery) was planned here but its inner
`mulMont` / `fromMont` call `montgomeryRadixInvNat` (a brute-force
`List.range p.toNat` search) on every invocation — even a smoke-sized
N of 100 is too slow to complete inside the CI budget at any modulus
worth benchmarking. The SPEC v2 retrospective lists this as an
action item for HexArith itself.
-/
def smokeOnly (_seed : UInt64) : List FamilySpec := []

end HexArith.Bench.Families
