# `HexArith` benchmark reference

This page documents the committed `HexArith` benchmark surface in
[`HexArith/Benchmark.lean`](/home/kim/hex/worktrees/858547d6/HexArith/Benchmark.lean).
It covers the currently checked-in fixture families, their stable case
names, and the CSV-style Lean entrypoints that materialize those cases.
It does not record timing results or claim any rendered benchmark
publication beyond the repository source tree.

## Benchmark families

### `Nat` extended GCD

- Cases live in `HexArith.Benchmark.natExtGcdCases`.
- Result rows come from `HexArith.Benchmark.runNatExtGcdCsv`.
- CSV header: `name,gcd,s,t`

Stable cases:

- `nat-coprime-small`
- `nat-composite-shared-factor`
- `nat-power-of-two-boundary`

### `Int` extended GCD

- Cases live in `HexArith.Benchmark.intExtGcdCases`.
- Result rows come from `HexArith.Benchmark.runIntExtGcdCsv`.
- CSV header: `name,gcd,s,t`

Stable cases:

- `int-mixed-sign-large`
- `int-both-negative`
- `int-asymmetric-magnitudes`

### `UInt64` extended GCD

- Cases live in `HexArith.Benchmark.uint64ExtGcdCases`.
- Result rows come from `HexArith.Benchmark.runUInt64ExtGcdCsv`.
- CSV header: `name,gcd,s,t`

Stable cases:

- `u64-coprime-near-word`
- `u64-shared-factor`
- `u64-fibonacci-shaped`

### Modular exponentiation

- Cases live in `HexArith.Benchmark.powModCases`.
- Result rows come from `HexArith.Benchmark.runPowModCsv`.
- CSV header: `name,value`

Stable cases:

- `powmod-small-prime`
- `powmod-large-base`
- `powmod-fermat-boundary`

### Barrett vs Montgomery reduction comparison

- Cases live in `HexArith.Benchmark.reductionComparisonCases`.
- Result rows come from `HexArith.Benchmark.runReductionComparisonCsv`.
- CSV header: `name,modulus,a,b,preference,barrett,montgomery`
- Preference tags are rendered with `ReductionPreference.csvTag` as one
  of `barrett`, `montgomery`, or `crossover`.
- Unsupported paths are rendered as `NA`.

Stable cases:

- `reduction-barrett-tiny`
- `reduction-barrett-upper-edge`
- `reduction-montgomery-crossover`

## Case scope

The current `HexArith` Phase 4 slice covers microbenchmarks for:

- extended GCD over `Nat`, `Int`, and `UInt64`
- modular exponentiation via `HexArith.powMod`
- the committed Barrett-versus-Montgomery crossover comparison cases

The reduction comparison rows report both executable paths when the
current implementation supports them. In the committed cases,
`reduction-barrett-upper-edge` has no Montgomery value and therefore
emits `NA` in the `montgomery` column.

## How to regenerate

The benchmark page is derived directly from the Lean runners in
[`HexArith/Benchmark.lean`](/home/kim/hex/worktrees/858547d6/HexArith/Benchmark.lean).
To regenerate the documented CSV-style outputs from Lean, import
`HexArith.Benchmark` and evaluate the runner definitions:

```lean
import HexArith.Benchmark

#eval HexArith.Benchmark.runNatExtGcdCsv
#eval HexArith.Benchmark.runIntExtGcdCsv
#eval HexArith.Benchmark.runUInt64ExtGcdCsv
#eval HexArith.Benchmark.runPowModCsv
#eval HexArith.Benchmark.runReductionComparisonCsv
```

Those definitions are the repository's current source of truth for the
named `HexArith` benchmark fixtures and exported columns.
