# Phase 1 Scaffolding Checkpoint 5

This checkpoint records the merge wave on `main` after
`HexManual/Phase1ScaffoldingCheckpoint-4.md`. The wave itself spans PRs
`#130` through `#158`; the live frontier below is cross-checked against
the current repository state after PR `#210` merged on
`2026-04-23T05:49:28Z`.

## Newly merged on `main` since the fourth checkpoint

### `HexModArith`

- PR `#130`: `HexModArith/Core.lean` adds inverse-candidate, inverse, and
  exponentiation scaffold declarations for `ZMod64`.
- PR `#148`: `HexModArith/Instances.lean` adds the ring, domain, and
  characteristic instance layer.
- PR `#157`: `HexModArith/Theorems.lean` adds the theorem cluster promised by
  the library spec.

### `HexGf2`

- PR `#132`: `HexGf2/Ops.lean` adds packed multiplication for `GF2Poly`.
- PR `#153`: `HexGf2/Ops.lean` adds packed division-with-remainder.
- PR `#158`: `HexGf2/Ops.lean` adds the packed GCD scaffold.

### `HexMatrixMathlib`

- PR `#133`: `HexMatrixMathlib/Determinant.lean` adds the determinant bridge
  statement layer.
- PR `#154`: `HexMatrixMathlib/Rank.lean` adds the row-echelon-rank to
  `Matrix.rank` correspondence theorem surface.

### Root-library conformance and bridge readiness

- PR `#140`: `HexPoly/Conformance.lean` begins the deterministic Phase 3
  conformance surface for arithmetic and division.
- PR `#142`: `HexArith/Conformance.lean` adds the first committed core
  conformance fixtures.
- PR `#144`: `HexMatrix/Conformance.lean` adds the first committed matrix-core
  conformance fixtures.
- PR `#143`: `HexPolyZMathlib/Dense.lean` adds the Mignotte-bound bridge layer
  on top of the earlier dense bridge scaffold.

### `HexGramSchmidt`

- PR `#149`: `HexGramSchmidt/Int.lean` adds the basis-span scaffold needed by
  downstream `HexLll` and Mathlib bridge work.

### Checkpointing

- PR `#131`: adds `HexManual/Phase1ScaffoldingCheckpoint-4.md`, closing the
  previous checkpoint issue and fixing the baseline for this wave.

## Current frontier

- The `#130`-`#158` wave finished the first broad Phase 1 pass for
  `HexModArith`, `HexGf2`, and most of `HexMatrixMathlib`, and it put the root
  libraries `HexArith`, `HexPoly`, and `HexMatrix` onto the modern
  conformance-module path.
- Later follow-on merges already moved some of that wave's immediate backlog:
  `HexModArith` Phase 1 is now reviewed complete (`#164` and `#181`),
  `HexGramSchmidt` Phase 1 is complete and Phase 2 is now open (`#168`,
  `#194`), `HexMatrixMathlib` gained its span bridge (`#198`), and
  `HexPolyZMathlib` has since advanced through Phase 1 into its Phase 2
  review queue (`#210`).
- As of authoring, the active queue is centered on `HexModArith -> Phase 3`,
  the root-library conformance fronts for `HexPoly` and `HexMatrix`, the
  `HexArith -> Phase 4` follow-on, and Phase 1 scaffolding for downstream
  libraries such as `HexGf2`, `HexLll`, `HexPolyFp`, `HexMatrixMathlib`,
  `HexModArithMathlib`, and `HexGramSchmidtMathlib`.

## Ready vs blocked state

`python3 scripts/status.py` currently reports these libraries as ready:

- `HexArith -> Phase 4`
- `HexPoly -> Phase 3`
- `HexMatrix -> Phase 3`
- `HexModArith -> Phase 3`
- `HexGramSchmidt -> Phase 2`
- `HexGf2 -> Phase 1`
- `HexLll -> Phase 1`
- `HexPolyFp -> Phase 1`
- `HexMatrixMathlib -> Phase 1`
- `HexModArithMathlib -> Phase 1`
- `HexGramSchmidtMathlib -> Phase 1`
- `HexPolyZMathlib -> Phase 2`

The remaining libraries are blocked, with immediate blockers grouped as
follows:

- Waiting on `HexPoly.done_through >= 3`: `HexPolyZ`, `HexPolyMathlib`
- Waiting on `HexPolyFp.done_through >= 1`: `HexGfqRing`, `HexHensel`,
  `HexGf2Mathlib`
- Waiting on `HexGfqRing.done_through >= 1`: `HexGfqField`, `HexBerlekamp`
- Waiting on `HexLll.done_through >= 1`: `HexLllMathlib`
- Waiting on `HexBerlekamp.done_through >= 1`: `HexConway`,
  `HexBerlekampMathlib`
- Waiting on later downstream combinations: `HexGfq`,
  `HexBerlekampZassenhaus`, `HexHenselMathlib`, `HexGfqMathlib`,
  `HexBerlekampZassenhausMathlib`

No library is fully done yet.
