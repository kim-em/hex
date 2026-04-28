# HexArith benchmarks

- Run: `f5c368aa10365e7722e576a92946638b5e5ad46b`
- Machine: chungus (CPU: AMD EPYC 9455 48-Core Processor)
- Date: 2026-04-23T12:39:47Z
- Toolchain: `leanprover/lean4:v4.30.0-rc2`
- Seed: `12648430`

Per-family detail follows; the **Summary** table at the end aggregates.

## A1.nat-extgcd

- Mode: measured (2 runs)
- Parameter: `65536` (origin: discovered)
- Statuses: ok
- Wall: median **137.18 ms**, min 137.04 ms, max 137.31 ms
- Comparator `python-stdlib`: median 282.70 ms (2 runs)

## A2.nat-powmod

- Mode: measured (2 runs)
- Parameter: `15808` (origin: discovered)
- Statuses: ok
- Wall: median **689.56 ms**, min 688.84 ms, max 690.29 ms
- Comparator `python-stdlib`: median 6.16 s (2 runs)

## A3.barrett-mulmod

- Mode: measured (2 runs)
- Parameter: `100000000` (origin: discovered)
- Statuses: ok
- Wall: median **553.14 ms**, min 553.08 ms, max 553.20 ms
- Comparator `python-stdlib`: median 10.10 s (2 runs)

## Summary

| family | param | origin | wall (median) | comparator | ratio (Lean/cmp) | log-log slope |
|---|---|---|---|---|---|---|
| A1.nat-extgcd | 65536 | discovered | 137.18 ms | 282.70 ms | 0.49× | — |
| A2.nat-powmod | 15808 | discovered | 689.56 ms | 6.16 s | 0.11× | — |
| A3.barrett-mulmod | 100000000 | discovered | 553.14 ms | 10.10 s | 0.05× | — |

## Honest assessment

_Hand-edit this section after each run with what surprised you, what calibration got wrong, and what the report doesn't yet capture._
