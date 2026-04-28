import HexLLL.Bench.Calibration
import HexLLL.Bench.Driver
import HexLLL.Bench.Inputs

/-!
# HexLLL benchmark family registry

Two budgeted families and (per the SPEC v2 plan) a `smokeOnly` slot.
-/

namespace HexLLL.Bench.Families

open HexLLL.Bench

/-- L1: uniform random integer basis, square. Param = dim n (snapped
to a discrete ladder by [Inputs.runL1](./Inputs.lean)). -/
def l1 (seed : UInt64) : FamilySpec :=
  { name := "L1.uniform-dim-sweep"
  , familyVersion := 1
  , paramName := "dim"
  , expectedSlope := 4.0
  , paramFloor := 4
  , paramCeiling := 8
  , initialGuess := Calibration.l1RandomDim
  , runOne := fun n => pure (Inputs.runL1 seed n) }

/-- L2: arith-heavy. Fixed dim n=20, sweep entry bit-width B. -/
def l2 (seed : UInt64) : FamilySpec :=
  { name := "L2.arith-bit-sweep"
  , familyVersion := 1
  , paramName := "bits"
  , expectedSlope := 2.0
  , paramFloor := 8
  , paramCeiling := 256
  , initialGuess := Calibration.l2ArithBits
  , runOne := fun bits => pure (Inputs.runL2 seed bits) }

/-- All budgeted families. -/
def all (seed : UInt64) : List (Float × FamilySpec) :=
  [ (0.50, l1 seed)
  , (0.50, l2 seed) ]

/-- Smoke-only families. None for HexLLL in this prototype — both
budgeted families are well-defined. -/
def smokeOnly (_seed : UInt64) : List FamilySpec := []

end HexLLL.Bench.Families
