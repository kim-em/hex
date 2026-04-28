# HexLLL benchmarks

- Run: `f5c368aa10365e7722e576a92946638b5e5ad46b`
- Machine: chungus (CPU: AMD EPYC 9455 48-Core Processor)
- Date: 2026-04-23T12:55:04Z
- Toolchain: `leanprover/lean4:v4.30.0-rc2`
- Seed: `12648430`

Per-family detail follows; the **Summary** table at the end aggregates.

## L1.uniform-dim-sweep

- Mode: measured (1 runs)
- Parameter: `8` (origin: predicted)
- Statuses: ok
- Wall: median **1.55 s**, min 1.55 s, max 1.55 s

## L2.arith-bit-sweep

- Mode: measured (1 runs)
- Parameter: `256` (origin: discovered)
- Statuses: ok
- Wall: median **35.46 ms**, min 35.46 ms, max 35.46 ms

## Summary

| family | param | origin | wall (median) | comparator | ratio (Lean/cmp) | log-log slope |
|---|---|---|---|---|---|---|
| L1.uniform-dim-sweep | 8 | predicted | 1.55 s | — | — | — |
| L2.arith-bit-sweep | 256 | discovered | 35.46 ms | — | — | — |

## Honest assessment

_Hand-edit this section after each run with what surprised you, what calibration got wrong, and what the report doesn't yet capture._
