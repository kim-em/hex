import HexArith.Bench.Calibration
import HexArith.Bench.Driver
import HexArith.Bench.Families
import HexArith.Bench.Inputs
import HexArith.Bench.Random

/-!
# `HexArith.Bench` — Phase 4 timed benchmark surface for HexArith

See [Main.lean](Bench/Main.lean) for the executable entry point and
[the project plan](../.claude/plans/let-s-make-a-plan-synchronous-token.md)
for the architecture.

This namespace is distinct from the older
[HexArith.Benchmark](Benchmark.lean) result-only fixture registry. The
two coexist; see [SPEC/benchmarking.md](../SPEC/benchmarking.md).
-/
