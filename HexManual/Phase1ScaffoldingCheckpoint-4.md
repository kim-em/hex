# Phase 1 Scaffolding Checkpoint 4

This checkpoint records the next merge wave now on `main` after `HexManual/Phase1ScaffoldingCheckpoint-3.md`. It reflects repository state after PR `#130` merged on `2026-04-23T03:10:26Z`; the issue body for this checkpoint listed ten merged PRs through `#126`, and `#130` landed before authoring completed.

## Newly merged on `main` since the third checkpoint

### `HexGramSchmidt`

- PR `#107`: `HexGramSchmidt/Int.lean` adds the Gram-determinant declarations for the integer scaffold.
- PR `#114`: `HexGramSchmidt/Rat.lean` adds the rational-basis and coefficient API layer.
- PR `#125`: `HexGramSchmidt/Update.lean` adds the size-reduction and adjacent-swap update scaffold.

### `HexGF2`

- PR `#108`: `HexGF2/FiniteExtension.lean` adds the packed finite-extension carrier records.
- PR `#123`: `HexGF2/Ops.lean` adds normalization, XOR-based addition, and shift operations for packed `GF2Poly` values.

### `HexPolyZ`

- PR `#109`: `HexPolyZ/Content.lean` adds the content and primitive-part scaffold.
- PR `#124`: `HexPolyZ/Content.lean` adds exact Mignotte coefficient and uniform bound declarations.
- PR `#122`: the Phase 1 review slice landed, moving `HexPolyZ` onto the Phase 3 queue once its upstream `HexPoly` conformance gate is complete.

### `HexArith` and downstream arithmetic

- PR `#113`: the `HexArith` Phase 2 review landed, so `python3 scripts/status.py` now reports `HexArith -> Phase 3 (conformance testing)` on the ready queue.
- PR `#118`: `HexModArith/Core.lean` adds the core `ZMod64` construction, arithmetic, reduction, and equality scaffold.
- PR `#130`: `HexModArith/Core.lean` extends that scaffold with `one`, inverse-candidate / inverse APIs, and exponentiation.

### Mathlib bridge reviews

- PR `#126`: the `HexPolyMathlib` Phase 2 review landed, taking that bridge library off the active ready queue until `HexPoly -> Phase 3` completes.

## Current frontier

- `HexModArith`, `HexGF2`, and `HexMatrixMathlib` remain the most visible Phase 1 scaffolding fronts on the active queue. `HexModArith` just absorbed two back-to-back scaffolding PRs, `HexGF2` is waiting on the focused multiplication slice from issue `#128`, and `HexMatrixMathlib` still has its determinant bridge issue `#117` in flight.
- The conformance-testing queue is now anchored by `HexArith`, `HexPoly`, and `HexMatrix`, which `python3 scripts/status.py` reports as ready for `PLAN/Phase3.md`.
- Two additional Phase 1 fronts are also ready and should not be overlooked: `HexGramSchmidt` remains open after its determinant/rational/update merge wave, and `HexPolyZMathlib` has become newly ready now that `HexPolyZ.done_through` advanced.

## Ready vs blocked state

`python3 scripts/status.py` currently reports these libraries as ready for work:

- `HexArith -> Phase 3`
- `HexPoly -> Phase 3`
- `HexMatrix -> Phase 3`
- `HexModArith -> Phase 1`
- `HexGramSchmidt -> Phase 1`
- `HexGF2 -> Phase 1`
- `HexMatrixMathlib -> Phase 1`
- `HexPolyZMathlib -> Phase 1`

The remaining libraries are blocked, with immediate blockers grouped as follows:

- Waiting on `HexPoly.done_through >= 3`: `HexPolyZ`, `HexPolyMathlib`
- Waiting on `HexModArith.done_through >= 1`: `HexPolyFp`, `HexModArithMathlib`
- Waiting on `HexGramSchmidt.done_through >= 1`: `HexLLL`, `HexGramSchmidtMathlib`
- Waiting on `HexPolyFp.done_through >= 1`: `HexGfqRing`, `HexHensel`
- Waiting on combined Phase 1 prerequisites: `HexBerlekamp`, `HexGF2Mathlib`, `HexBerlekampMathlib`, `HexBerlekampZassenhausMathlib`
- Waiting on later downstream combinations: `HexGfqField`, `HexConway`, `HexGfq`, `HexBerlekampZassenhaus`, `HexLLLMathlib`, `HexHenselMathlib`, `HexGfqMathlib`

No library is fully done yet.
