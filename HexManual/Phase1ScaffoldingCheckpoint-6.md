# Phase 1 Scaffolding Checkpoint 6

This checkpoint records the merge wave on `main` after
`HexManual/Phase1ScaffoldingCheckpoint-5.md`. The planned wave spans PRs
`#217`, `#219`, `#221`, `#222`, `#223`, `#225`, `#226`, `#231`, `#232`,
`#234`, and `#238`; the live frontier below is cross-checked against the
current repository state after PR `#240` merged on `2026-04-23T06:31:16Z`.

## Newly merged on `main` since the fifth checkpoint

### `HexGramSchmidt` and its Mathlib bridge

- PR `#217`: `HexGramSchmidtMathlib/Bridge.lean` adds the first Mathlib
  bridge scaffold for rational and integer Gram-Schmidt data.
- PR `#219`: records the `HexGramSchmidt` Phase 2 scaffold review, moving the
  base library from active implementation into the conformance wait state.

### `HexPolyFp`, `HexGF2`, and downstream frontier opening

- PR `#221`: `HexPolyFp/Frobenius.lean` adds the Frobenius and modular-power
  theorem surface promised by the Phase 1 spec.
- PR `#232`: marks `HexPolyFp` Phase 1 complete, which in turn opens
  `HexGfqRing -> Phase 1` and `HexHensel -> Phase 1`.
- PR `#234`: marks `HexGF2` Phase 1 complete, moving that library onto its
  Phase 2 scaffold review queue.

### `HexLLL`

- PR `#222`: `HexLLL/State.lean` adds the state carrier and Gram-data access
  surface for the LLL pipeline.
- PR `#238`: `HexLLL/SizeReduce.lean` adds the first executable size-reduction
  transition, giving the library its first algorithmic Phase 1 slice.

### `HexModArithMathlib` and `HexModArith`

- PR `#226`: completes the `HexModArithMathlib` Phase 1 bridge scaffold around
  the `ZMod64` representation boundary.
- PR `#223`: `HexModArith/Conformance.lean` adds a substantial inverse-focused
  conformance slice for the base modular-arithmetic library.

### Reviews and checkpointing

- PR `#225`: records the `HexMatrixMathlib` Phase 2 scaffold review.
- PR `#231`: records the `HexPolyZMathlib` Phase 2 scaffold review.

## Current frontier

- The `#217`-`#238` wave finished Phase 1 for `HexPolyFp` and `HexGF2`,
  advanced `HexGramSchmidtMathlib` into active scaffolding, and pushed
  `HexLLL` from static declarations into executable transition code.
- Those merges also changed the dependency graph materially: `HexGfqRing` and
  `HexHensel` are now live Phase 1 branches instead of blocked downstream
  work, while `HexGF2` and `HexPolyFp` have shifted from implementation to
  review.
- Live state has moved slightly beyond the original issue scope during
  authoring: PR `#235` added another substantial `HexModArith` Phase 3
  conformance slice and PR `#240` recorded the `HexModArithMathlib` Phase 2
  review, but `HexModArith` itself still remains on the active Phase 3
  frontier.

## Ready vs blocked state

`python3 scripts/status.py` currently reports these libraries as ready:

- `HexArith -> Phase 4`
- `HexPoly -> Phase 3`
- `HexMatrix -> Phase 3`
- `HexModArith -> Phase 3`
- `HexGF2 -> Phase 2`
- `HexLLL -> Phase 1`
- `HexPolyFp -> Phase 2`
- `HexGfqRing -> Phase 1`
- `HexHensel -> Phase 1`
- `HexGramSchmidtMathlib -> Phase 1`

The remaining libraries are blocked, with immediate blockers grouped as
follows:

- Waiting on core-library Phase 3 conformance: `HexGramSchmidt`,
  `HexPolyZ`, `HexPolyMathlib`, `HexMatrixMathlib`, and
  `HexModArithMathlib` all now depend on their corresponding base
  libraries clearing Phase 3.
- Waiting on `HexGfqRing.done_through >= 1`: `HexGfqField` and
  `HexBerlekamp`.
- Waiting on `HexLLL.done_through >= 1`: `HexLLLMathlib`.
- Waiting on `HexHensel.done_through >= 1` and `HexBerlekamp.done_through >= 1`:
  `HexBerlekampZassenhaus` remains closed until both the finite-field and
  Hensel branches land.
- Waiting on later downstream combinations: `HexConway`, `HexGfq`,
  `HexBerlekampMathlib`, `HexHenselMathlib`, `HexGF2Mathlib`,
  `HexGfqMathlib`, and `HexBerlekampZassenhausMathlib`.

## Bottlenecks to watch

- The dominant shared bottleneck is still Phase 3 conformance in the base
  libraries `HexPoly` and `HexMatrix`, which gate both the core branches and
  their Mathlib follow-ons.
- `HexModArith` remains an active conformance front rather than a completed
  dependency, so `HexModArithMathlib` is still waiting behind that same base
  library Phase 3 gate even after its Phase 2 review landed.
- `HexGfqRing` is now the key newly opened branch because it gates both
  `HexGfqField` and `HexBerlekamp`, which in turn gate most of the finite-field
  and factorisation stack.
- `HexHensel` is newly actionable and directly relevant to the later
  `HexBerlekampZassenhaus` and `HexHenselMathlib` path, but it is no longer the
  unique downstream bottleneck because finite-field quotient work is still
  ahead of much of that stack.
- The immediate review queue is now `HexGF2 -> Phase 2` and
  `HexPolyFp -> Phase 2`, while active implementation work remains concentrated
  in `HexLLL`, `HexGfqRing`, `HexHensel`, and the remaining base-library
  conformance fronts.
