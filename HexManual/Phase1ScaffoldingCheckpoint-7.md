# Phase 1 Scaffolding Checkpoint 7

This checkpoint records the merge wave on `main` after
`HexManual/Phase1ScaffoldingCheckpoint-6.md`. The planned wave spans PRs
`#286`, `#288`, `#289`, `#292`, `#295`, `#297`, `#298`, `#299`, `#300`,
`#301`, `#306`, `#310`, `#311`, `#316`, `#317`, `#319`, `#320`, `#323`,
`#324`, `#325`, `#326`, `#330`, `#331`, `#335`, `#338`, `#339`, `#340`,
`#343`, `#344`, `#345`, `#352`, `#356`, `#357`, `#358`, `#359`, `#360`,
`#362`, `#363`, `#368`, `#372`, `#373`, `#382`, and `#385`; the live
frontier below is cross-checked against the current repository state after
PR `#385` merged on `2026-04-23T10:10:38Z`.

## Newly merged on `main` since the sixth checkpoint

### `HexBerlekamp`, `HexHensel`, and `HexGF2Mathlib`

- PRs `#295`, `#316`, `#323`, `#335`, `#357`, and `#372` build out the
  `HexBerlekamp` scaffold stack: matrix surface, kernel surface,
  irreducibility entrypoints, split-step declarations, Rabin surface, and
  the first distinct-degree shell.
- PRs `#298` and `#299` expand `HexHensel` with a public precision wrapper
  and a multifactor scaffold layer, materially widening the executable API
  promised by the Phase 1 spec.
- PR `#362` opens `HexGF2Mathlib` with the first `GF2Poly` bridge entrypoint,
  giving the finite-field bridge stack a real base to extend.

### `HexGfqRing`, `HexGF2`, `HexPolyMathlib`, and `HexPolyZ`

- PR `#286` completes the `HexGfqRing` Phase 2 scaffold review, moving the
  library onto the live Phase 3 conformance frontier.
- PR `#358` adds the first committed `HexGfqRing` conformance slice around
  quotient-core operations; the follow-on unit/cast slice remains in the live
  repair queue rather than the merged baseline.
- PRs `#360` and `#373` push `HexGF2` deeper into Phase 3 with packed-core and
  Euclidean conformance coverage.
- PR `#339` adds the first `HexPolyMathlib` conformance slice around the
  explicit bridge fixtures now expected by the Phase 3 plan.
- PRs `#317` and `#382` extend `HexPolyZ` conformance through its Mignotte
  and coefficient-bound surface, moving the base library off the old Phase 3
  frontier.

### `HexArith` and `HexPoly` benchmarking

- PRs `#292`, `#297`, and `#326` give `HexArith` benchmark fixtures, an
  executable reduction runner, and CSV export support, completing the
  project-visible Phase 4 benchmark publication slice for that library.
- PRs `#359` and `#385` do the same for `HexPoly`: benchmark fixtures first,
  then stable CSV export rows and batch runners for multiplication,
  division, and GCD/XGCD cases.

### `HexLLL` and `HexGfqField`

- PRs `#288`, `#306`, `#320`, and `#330` move `HexLLL` from loop entrypoints
  into reducedness predicates, theorem scaffolds, and the first matrix
  benchmark fixtures, but do not yet finish Phase 1.
- PRs `#289`, `#310`, and `#319` plus review PRs `#325` and `#356` finish the
  current `HexGfqField` Phase 1 scaffold wave and its attestation, while
  PR `#345` rewrites wrong-but-plausible scaffold bodies into honest
  placeholders before later work builds on them.

### `HexMatrix`, `HexGramSchmidt`, and review/rewind cleanup

- PR `#300` adds a `HexGramSchmidt` Phase 3 basis and determinant
  conformance slice, while PR `#338` begins the corresponding
  `HexMatrixMathlib` determinant-bridge conformance surface.
- PR `#331` tightens project rules by forbidding wrong-but-plausible
  scaffolds and sharpening the expected conformance style.
- PR `#352` rewinds stale `HexMatrix` and `HexGramSchmidt` review state after
  that rule change, PR `#343` adds a shared matrix literal helper needed by
  later fixtures, PR `#344` removes scaffold-locking conformance guards, PR
  `#363` records the refreshed `HexMatrix` review blockers, and PR `#368`
  replaces the dishonest free-column and nullspace stubs with honest
  placeholders.

## Current frontier

- The checkpoint-7 wave shifts the main project frontier away from generic
  Phase 1 expansion and toward three distinct tracks: Phase 4 benchmark
  publication for `HexArith` and `HexPoly`, Phase 3 conformance growth for
  `HexGF2`, `HexGfqRing`, and `HexPolyMathlib`, and remaining Phase 1
  scaffolding in `HexBerlekamp`, `HexHensel`, `HexGF2Mathlib`, and `HexLLL`.
- The live queue now also has a visible repair component: open failing PRs on
  the `HexGfqRing` unit/cast slice and the `HexPolyMathlib` explicit-fixture
  slice sit directly on top of otherwise-ready Phase 3 work, while the
  matrix-family rewind still leaves `HexGramSchmidt` follow-on conformance in
  repair or replan territory.
- `HexPolyZ` is no longer an active Phase 3 branch; it now waits behind
  `HexPoly.done_through >= 4` for its own Phase 4 work, while
  `HexPolyZMathlib` waits only on `HexPolyMathlib.done_through >= 3`.
- The matrix-family rewind is still active project context: `HexMatrix` and
  `HexGramSchmidt` both fell back to Phase 2 review after the project-wide
  honesty rule tightened, so later benchmark and bridge work in that area is
  downstream of review restoration rather than new feature breadth.

## Ready vs blocked state

`python3 scripts/status.py` currently reports these libraries as ready:

- `HexArith -> Phase 4`
- `HexPoly -> Phase 4`
- `HexMatrix -> Phase 2`
- `HexGramSchmidt -> Phase 2`
- `HexGF2 -> Phase 3`
- `HexLLL -> Phase 1`
- `HexGfqRing -> Phase 3`
- `HexBerlekamp -> Phase 1`
- `HexHensel -> Phase 1`
- `HexPolyMathlib -> Phase 3`
- `HexGF2Mathlib -> Phase 1`

The remaining libraries are blocked, with immediate blockers grouped as
follows:

- Waiting on Phase 4 completion in upstream arithmetic and polynomial
  libraries: `HexModArith`, `HexPolyZ`, and `HexPolyFp`.
- Waiting on `HexGfqRing.done_through >= 3`: `HexGfqField`.
- Waiting on newly expanded Phase 1 finite-field and factorisation work:
  `HexConway`, `HexBerlekampZassenhaus`, `HexBerlekampMathlib`,
  `HexHenselMathlib`, `HexGfq`, and `HexGfqMathlib`.
- Waiting on restored or completed upstream conformance in the matrix and
  bridge stack: `HexMatrixMathlib`, `HexGramSchmidtMathlib`,
  `HexPolyZMathlib`, and `HexLLLMathlib`.
- Waiting on the still-closed `HexBerlekampZassenhaus` base path:
  `HexBerlekampZassenhausMathlib`.

No library is fully done yet.

## Bottlenecks to watch

- `HexPoly -> Phase 4` is now the key shared benchmark bottleneck. Until it
  completes, `HexPolyZ` and `HexPolyFp` cannot move into their own Phase 4
  work.
- `HexGfqRing -> Phase 3` is the main conformance bottleneck for the
  finite-field stack. `HexGfqField` is now blocked only on that phase gate,
  and the broader `HexConway` / `HexGfq` / Mathlib path stays behind it.
- `HexBerlekamp` and `HexHensel` are both materially broader than they were at
  checkpoint 6, but they still block the whole Zassenhaus branch until the
  remaining Phase 1 shell work lands.
- `HexMatrix` and `HexGramSchmidt` are no longer bottlenecked by missing
  breadth; they are bottlenecked by review honesty. Restoring trustworthy
  Phase 2 state there is a prerequisite for later conformance and benchmark
  work to mean what the status graph says they mean.
