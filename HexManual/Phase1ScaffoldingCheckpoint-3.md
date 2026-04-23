# Phase 1 Scaffolding Checkpoint 3

This checkpoint records the next scaffolding merge wave now on `main` after `HexManual/Phase1ScaffoldingCheckpoint-2.md`. It reflects repository state after PR `#100` merged on `2026-04-23T02:29:01Z`.

## Newly merged on `main` since the second checkpoint

### `HexArith`

- PR `#73`: `HexArith/Binomial.lean` adds the Phase 1 binomial and Fermat witness surface.
- PR `#76`: `HexArith/ExtGcd.lean` attaches the `@[extern "lean_hex_mpz_gcdext"]` GMP scaffold for `Int.extGcd`.
- PR `#97`: `HexArith/Montgomery/InvNat.lean` and `HexArith/Montgomery/Context.lean` add the residual Montgomery inverse/context declarations that the spec still named after the earlier review attempt.

### `HexPoly`

- PR `#81`: `HexPoly/Crt.lean` tightens the CRT remainder-side contract around the monic assumptions.
- PR `#82`: `HexPoly/Gcd.lean` narrows the field-division boundary in the GCD scaffold.
- PR `#77`: `libraries.yml` advances `HexPoly.done_through` to `3`, marking the library ready through the Phase 3 conformance-testing review.

### `HexMatrix`

- PR `#84`: `libraries.yml` advances `HexMatrix.done_through` to `3`, marking the library ready through the Phase 3 conformance-testing review.
- PR `#86`: `HexMatrix/RowEchelon.lean` adds the `Vector.normSq` helper and its `normSq_eq_dot` theorem for downstream linear-algebra scaffolding.

### `HexPolyMathlib`

- PR `#87`: `HexPolyMathlib/DensePoly.lean` adds the initial `DensePoly`/`Polynomial` conversion scaffold and bridge equivalence.
- PR `#100`: `HexPolyMathlib/Gcd.lean` adds the first GCD and extended-GCD correspondence declarations on top of that bridge.

### `HexMatrixMathlib`

- PR `#90`: `HexMatrixMathlib/MatrixEquiv.lean` adds the first concrete matrix equivalence bridge between project matrices and Mathlib matrices.

### `HexPolyZ`

- PR `#85`: `HexPolyZ/Core.lean` adds the `ZPoly` alias together with the initial congruence and coprimality-over-`ZMod p` scaffold.

### `HexGF2`

- PR `#96`: `HexGF2/Core.lean` and `HexGF2/ffi/clmul.c` add the packed `GF2Poly` core plus the carry-less multiply FFI boundary and fallback implementation.

### `HexGramSchmidt`

- PR `#98`: `HexGramSchmidt/Int.lean` adds the first integer-basis and coefficient scaffold slice.

## Current frontier

- `HexArith` remains the main correctness gate. `python3 scripts/status.py` still reports `HexArith -> Phase 1`, and issue `#89` is the active review/sign-off pass that decides whether `libraries.yml` can advance.
- `HexMatrixMathlib` has another Phase 1 slice in flight through PR `#99` / issue `#92`, covering row-operation correspondence on top of the merged matrix equivalence bridge.
- `HexGramSchmidt` immediately opened a follow-on Phase 1 issue, `#101`, for Gram determinants and scaled-coefficient declarations.
- The queue is otherwise notably narrower than at the previous checkpoint: the root-library Phase 3 reviews for `HexPoly` and `HexMatrix` have landed, and several downstream Phase 1 libraries now have their first scaffolding slices on `main`.

## Ready vs blocked state

`python3 scripts/status.py` currently reports these libraries as ready for work:

- `HexArith -> Phase 1`
- `HexPoly -> Phase 3`
- `HexMatrix -> Phase 3`
- `HexGramSchmidt -> Phase 1`
- `HexGF2 -> Phase 1`
- `HexPolyZ -> Phase 1`
- `HexPolyMathlib -> Phase 1`
- `HexMatrixMathlib -> Phase 1`

The remaining libraries are still blocked, with the immediate blockers grouped as follows:

- Waiting on `HexArith.done_through >= 1`: `HexModArith`
- Waiting on `HexGramSchmidt.done_through >= 1`: `HexLLL`
- Waiting on `HexModArith.done_through >= 1`: `HexPolyFp`, `HexModArithMathlib`
- Waiting on `HexPolyFp.done_through >= 1`: `HexGfqRing`, `HexGF2Mathlib`
- Waiting on `HexGfqRing.done_through >= 1`: `HexGfqField`, `HexBerlekamp`
- Waiting on `HexPolyZ.done_through >= 1`: `HexHensel`, `HexPolyZMathlib`
- Waiting on later downstream combinations: `HexConway`, `HexGfq`, `HexBerlekampZassenhaus`, `HexGramSchmidtMathlib`, `HexLLLMathlib`, `HexBerlekampMathlib`, `HexHenselMathlib`, `HexGfqMathlib`, `HexBerlekampZassenhausMathlib`

No library is fully done yet.
