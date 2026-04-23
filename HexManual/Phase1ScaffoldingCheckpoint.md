# Phase 1 Scaffolding Checkpoint

This checkpoint records the initial Phase 1 scaffolding now merged on `main` for the three libraries currently in active bootstrap: `HexArith`, `HexPoly`, and `HexMatrix`. It is a snapshot of repository state after the merge wave ending with PRs `#31` and `#22` on 2026-04-23.

## Merged on `main`

### `HexArith`

- PR `#10`: `HexArith/UInt64/Wide.lean` adds the shared wide-word helper surface.
- PR `#17`: `HexArith/Barrett/Context.lean` scaffolds the Barrett reduction context API.
- PR `#21`: `HexArith/Barrett/ReduceNat.lean` and `HexArith/Barrett/Reduce.lean` add Nat-level and executable Barrett reduction layers.
- PR `#26`: `HexArith/Montgomery/Context.lean` scaffolds the Montgomery context API.
- PR `#31`: `HexArith/Montgomery/RedcNat.lean` adds the Nat-level Montgomery REDC scaffold.

Current root re-export: `HexArith.lean`.

### `HexPoly`

- PR `#7`: `HexPoly/DensePoly.lean` adds the dense polynomial representation scaffold.
- PR `#13`: `HexPoly/Arithmetic.lean` adds the basic arithmetic operator surface.
- PR `#18`: `HexPoly/Division.lean` adds quotient/remainder scaffolding.

Current root re-export: `HexPoly.lean`.

### `HexMatrix`

- PR `#9`: `HexMatrix/RowEchelon.lean` adds the row-echelon data and proposition layer.
- PR `#16`: `HexMatrix/RowOps.lean` adds elementary row-operation scaffolding.
- PR `#22`: `HexMatrix/Rref.lean` adds the separate `rref` and free-column partition API surface.

Current root re-export: `HexMatrix.lean`.

## Open Phase 1 Frontier

The current follow-on work remains tracked separately and should be read as the immediate frontier, not as gaps to be replanned here.

- Issue `#27` (`feature`): add `HexMatrix` span-membership scaffolding.
- Issue `#28` (`feature`): add `HexPoly` GCD and Bezout scaffolding.
- PR `#32` / issue `#24`: `HexPoly` evaluation and composition scaffold is open and currently mergeable with passing checks.
- PR `#25` / issue `#19`: `HexArith` Nat extended-GCD scaffold is open but currently conflicting.
- Issue `#30` (`feature`, claimed): repair PR `#25` back to a mergeable state.

## Downstream Libraries Still Blocked

`scripts/status.py` still reports the three active libraries as `Ready` rather than complete, so every downstream library remains blocked on one or more of these fronts.

- Blocked on `HexArith`: `HexModArith`, `HexPolyFp`, `HexModArithMathlib`, `HexBerlekampMathlib`.
- Blocked on `HexPoly`: `HexGf2`, `HexPolyZ`, `HexPolyFp`, `HexPolyMathlib`, `HexHensel`, `HexGf2Mathlib`, `HexPolyZMathlib`, `HexHenselMathlib`, `HexBerlekampZassenhaus`, `HexBerlekampZassenhausMathlib`.
- Blocked on `HexMatrix`: `HexGramSchmidt`, `HexBerlekamp`, `HexMatrixMathlib`.
- Transitively blocked beyond those: `HexLll`, `HexGramSchmidtMathlib`, `HexGfqRing`, `HexGfqField`, `HexConway`, `HexGfq`, and `HexGfqMathlib`.

No library is yet marked fully done in `scripts/status.py`.
