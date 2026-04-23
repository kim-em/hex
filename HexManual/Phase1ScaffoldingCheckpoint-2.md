# Phase 1 Scaffolding Checkpoint 2

This checkpoint records the second scaffolding merge wave now on `main` for the active root libraries. It supersedes the earlier snapshot in `HexManual/Phase1ScaffoldingCheckpoint.md` and reflects repository state after PR `#64` merged on 2026-04-23T01:47:56Z.

## Newly merged on `main` since the first checkpoint

### `HexArith`

- PR `#25`: `HexArith/ExtGcd.lean` adds the Nat extended-GCD scaffold.
- PR `#39`: `HexArith/PowMod.lean` adds the modular exponentiation API surface.
- PR `#40`: `HexArith/Montgomery/InvNat.lean` extends the Montgomery context with inverse scaffolding.
- PR `#50`: `HexArith/Montgomery/Redc.lean` adds the UInt64-facing REDC bridge.
- PR `#54`: `HexArith/ExtGcd.lean` extends the scaffold with Int extended-GCD declarations.
- PR `#59`: `HexArith/ExtGcd.lean` extends the same module with UInt64 extended-GCD declarations.

Current root re-export: `HexArith.lean`.

### `HexPoly`

- PR `#32`: `HexPoly/Eval.lean` adds evaluation and composition scaffolding.
- PR `#35`: `HexPoly/Gcd.lean` adds the polynomial GCD and Bezout API surface.
- PR `#44`: `HexPoly/Crt.lean` adds Chinese remainder scaffolding.
- PR `#55`: `HexPoly/Content.lean` adds content, primitive-part, and normalization declarations.
- PR `#60`: Phase 1 review/sign-off lands in `libraries.yml`, moving `HexPoly.done_through` to `2`.

Current root re-export: `HexPoly.lean`.

### `HexMatrix`

- PR `#43`: `HexMatrix/Span.lean` adds the span-membership scaffold.
- PR `#49`: `HexMatrix/Nullspace.lean` adds nullspace witness and correctness declarations.
- PR `#53`: `HexMatrix/Determinant.lean` and `HexMatrix/RowOps.lean` add the Leibniz determinant surface together with row-operation determinant theorems.
- PR `#64`: `HexMatrix/Determinant.lean` adds the public Bareiss determinant API names required by the spec.

Current root re-export: `HexMatrix.lean`.

## Current frontier

- `HexArith` no longer has an open Phase 1 feature issue in the queue, but `python3 scripts/status.py` still reports it as `Ready -> Phase 1`, so a review/sign-off pass has not yet advanced `libraries.yml`.
- `HexPoly` has cleared its Phase 1 scaffold review via PR `#60`; it now appears in `scripts/status.py` as `Ready -> Phase 2 (scaffolding review)`.
- `HexMatrix` remains the active root-library frontier. Open issue `#61` tracks the residual echelon and column-partition declarations still needed before a fresh Phase 1 review can succeed; issue `#58` remains open in `replan` state pending that residual work.

## Downstream readiness and remaining blocks

`python3 scripts/status.py` now shows three downstream libraries newly ready for Phase 1 scaffolding because `HexPoly` is no longer the blocker:

- `HexGf2`
- `HexPolyZ`
- `HexPolyMathlib`

The remaining blocked libraries are:

- Blocked on `HexArith.done_through >= 1`: `HexModArith`
- Blocked on `HexMatrix.done_through >= 1`: `HexGramSchmidt`, `HexMatrixMathlib`
- Blocked on `HexModArith.done_through >= 1`: `HexPolyFp`, `HexModArithMathlib`
- Blocked on later dependencies downstream of those roots: `HexLll`, `HexGfqRing`, `HexGfqField`, `HexBerlekamp`, `HexHensel`, `HexConway`, `HexGfq`, `HexBerlekampZassenhaus`, `HexGramSchmidtMathlib`, `HexPolyZMathlib`, `HexLllMathlib`, `HexBerlekampMathlib`, `HexHenselMathlib`, `HexGf2Mathlib`, `HexGfqMathlib`, `HexBerlekampZassenhausMathlib`

In short: `HexPoly` has moved past Phase 1, `HexArith` is ready for review, and `HexMatrix` is down to the residual declarations tracked in `#61`.
