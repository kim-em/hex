# `HexPoly` Benchmark Reference

This page documents the currently committed `HexPoly` Phase 4 benchmark
surface from [HexPoly/Benchmark.lean](/home/kim/hex/worktrees/61785362/HexPoly/Benchmark.lean:1).
It is intentionally narrow: only the benchmark families, stable case
names, and CSV-style export entrypoints that already exist in the
library are listed here.

## Export entrypoints

`HexPoly.Benchmark` exposes three benchmark families and one CSV runner
for each family:

- `runMulCsv` for multiplication cases
- `runDivModMonicCsv` for monic division-with-remainder cases
- `runGcdCsv` for GCD/XGCD cases

Each runner returns a `List String` whose first element is a stable CSV
header and whose remaining elements are stable case rows.

## Multiplication

Runner: `HexPoly.Benchmark.runMulCsv`

Header: `name,coeffs`

Committed cases:

- `mul-small-dense`
  Input degrees: left `2`, right `2`
- `mul-medium-sparse`
  Input degrees: left `6`, right `5`

The `coeffs` column stores the output coefficient list as a single CSV
field with semicolon-separated entries.

## Monic division

Runner: `HexPoly.Benchmark.runDivModMonicCsv`

Header: `name,quotient,remainder`

Committed cases:

- `divmodmonic-small-exact`
  Dividend degree `3`, divisor degree `1`
- `divmodmonic-medium-inexact`
  Dividend degree `6`, divisor degree `2`

The `quotient` and `remainder` columns store coefficient lists as single
CSV fields with semicolon-separated entries.

## GCD and XGCD

Runner: `HexPoly.Benchmark.runGcdCsv`

Header: `name,gcd,s,t`

Committed cases:

- `gcd-small-linear`
  Input degrees: left `2`, right `1`
- `gcd-medium-quadratic`
  Input degrees: left `4`, right `3`

The `gcd`, `s`, and `t` columns store rational coefficient lists as
single CSV fields with semicolon-separated entries. The rows come from
the committed `xgcd` workloads in `HexPoly/Benchmark.lean`.

## How To Regenerate

The committed source of truth is the Lean module
[HexPoly/Benchmark.lean](/home/kim/hex/worktrees/61785362/HexPoly/Benchmark.lean:1).
To regenerate the CSV rows for this page, load `HexPoly.Benchmark` in a
Lean session and evaluate the exported runners directly:

```lean
#eval HexPoly.Benchmark.runMulCsv
#eval HexPoly.Benchmark.runDivModMonicCsv
#eval HexPoly.Benchmark.runGcdCsv
```

If any case names, headers, or runner names change in that module, this
page should be updated in the same PR.
