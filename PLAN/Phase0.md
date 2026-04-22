# Phase 0: Monorepo Scaffolding

**Coupling:** global. One-time repo-level bootstrap; not tracked
per-library in `libraries.yml`. Its completion is observable by the
existence of `lakefile.toml`, `scripts/check_dag.py`, etc.

One-time setup. Create the Lake monorepo infrastructure by reading the
spec and this document.

The repository begins markdown-only (`SPEC/`, `PLAN.md`, `PLAN/`,
`libraries.yml`, `AGENTS.md`, `.claude/CLAUDE.md`). Phase 0 is
responsible for creating the infrastructure needed in the repository
before we can start development work. Treat it as a single
`--critical-path` feature issue handled by one worker; do not fan out
into Phase 1 until the Phase 0 PR lands on `main`.

## Steps

1. Create `lean-toolchain` containing exactly
   `leanprover/lean4:v4.30.0-rc2`. This is the project baseline; do
   not substitute a different release.

2. Create `lakefile.toml` with one `[[lean_lib]]` per library in
   `libraries.yml` (the 27 computational + bridge libraries), plus
   one additional `[[lean_lib]]` for `HexManual` (the Verso-based
   documentation aggregator — see [Phase7.md](Phase7.md)). All
   `-mathlib` bridge libraries depend on the Mathlib tag
   `v4.30.0-rc2`. `HexManual` depends on Verso and on every `hex-*`
   library.

   Each computational/bridge library entry needs:
   - `name` — PascalCase (e.g. `HexArith`, `HexPolyZMathlib`)
   - Mathlib bridge libraries should declare `needs = ["mathlib"]`

3. Create empty root files and source directories for every library
   listed in `libraries.yml`:
   - `HexArith.lean` (empty or minimal) + `HexArith/` directory
   - `HexPoly.lean` + `HexPoly/`
   - ... (one pair per library in the DAG)
   - `HexModArithMathlib.lean` + `HexModArithMathlib/`
   - ... (one pair per mathlib bridge)

   Also create `HexManual.lean` + `HexManual/` for the documentation
   aggregator (empty at Phase 0 — chapters are authored per-library
   during Phase 7).

4. Write `scripts/check_dag.py` — a Python script that enforces the
   DAG defined by `libraries.yml`. It should:

   **Structural checks:**
   - Verify the graph is acyclic (topological sort succeeds).
   - Every dependency in `libraries.yml` names an existing entry.
   - Every `libraries.yml` entry has a matching `[[lean_lib]]` in
     `lakefile.toml` (parse TOML via `tomllib`, available since 3.11).
   - Every `[[lean_lib]]` in `lakefile.toml` either has a matching
     `libraries.yml` entry, or is on a known-exceptions list
     (currently: just `HexManual`).
   - Every library's root `.lean` file exists on disk.

   **Import boundary checks:**
   - For each `.lean` file (excluding `.lake/`), determine its library
     from the file path (top-level directory or root file name).
   - For each `import` statement, verify the imported module belongs to
     the same library, a declared dependency, or stdlib/core.
   - If the import starts with `Mathlib`, verify the library has
     `mathlib: true` in `libraries.yml` (or is `HexManual`, which may
     import from any hex-* library and from Verso, but not from
     Mathlib directly unless any `hex-*-mathlib` chapter it aggregates
     requires it).
   - Exit non-zero on any violation, printing all violations to stderr.

5. Write `scripts/status.py` — a Python script that queries
   `libraries.yml` and the phase-dependency table in
   [Conventions.md](Conventions.md). Its audience is the **planner
   agent**: the output is a survey of every ready `(library, phase)`
   pair, annotated with the SPEC and PLAN files the planner should
   consult before creating issues for that pair. Target behaviour:

   - Inputs: `libraries.yml`, the phase-dep rule table (encoded as
     a constant in the script — the authoritative copy is the table
     in [Conventions.md](Conventions.md); script and doc must agree).

   - **`scripts/status.py` (no args)** — lists every ready
     `(library, phase)` pair, every blocked pair with its blockers,
     and every fully-done library. The planner surveys the ready
     list and creates issues for whichever pairs to dispatch this
     cycle. Example output shape:

     ```
     Ready (dispatch issues in parallel):

       HexArith → Phase 1 (library scaffolding)
         spec: SPEC/Libraries/hex-arith.md
         plan: PLAN/Phase1.md
         on complete: libraries.yml HexArith.done_through: 1

       HexPoly → Phase 1 (library scaffolding)
         spec: SPEC/Libraries/hex-poly.md
         plan: PLAN/Phase1.md
         on complete: libraries.yml HexPoly.done_through: 1

       HexMatrix → Phase 1 (library scaffolding)
         spec: SPEC/Libraries/hex-matrix.md
         plan: PLAN/Phase1.md
         on complete: libraries.yml HexMatrix.done_through: 1

     Blocked:

       HexModArith → Phase 1
         waiting on: HexArith.done_through ≥ 1

       HexPolyFp → Phase 1
         waiting on: HexPoly.done_through ≥ 1, HexModArith.done_through ≥ 1

       ... (one entry per blocked library)

     Fully done: (none yet)
     ```

     The script emits one entry per library. The `spec` path is
     computed from the PascalCase library name via the naming
     convention in [Conventions.md](Conventions.md) — e.g.
     `HexPolyZMathlib` → `SPEC/Libraries/hex-poly-z-mathlib.md`.
     Do **not** emit a "next up" / single-recommendation line: the
     planner needs the full menu of ready pairs so it can choose
     which to dispatch this cycle based on current open-issue
     coverage, worker capacity, and DAG fan-out (see
     [../PLAN.md](../PLAN.md) "Survey and dispatch"). A single
     recommendation would bias the planner toward one library per
     cycle and kill parallelism.

   - **`scripts/status.py <Library>`** — same format but scoped to
     one library: its current `done_through`, whether it's ready
     to advance, what's blocking it if not, and the SPEC + PLAN
     files to read for the next phase.

   - **`scripts/status.py release <N>`** — evaluates release-N
     readiness against the predicate in [Releases.md](Releases.md);
     prints the missing libraries (with the specific `done_through`
     they need to reach) and whether the integration example exists
     and builds.

   - Exit non-zero on malformed `libraries.yml` or disagreement
     between `libraries.yml` and `lakefile.toml`.

6. Set up CI using `leanprover/lean-action`.

   **`.github/workflows/ci.yml`** (required, runs on every push/PR):
   ```yaml
   name: CI
   on: [push, pull_request]
   jobs:
     build:
       runs-on: ubuntu-latest
       steps:
         - uses: actions/checkout@v4
         - run: python3 scripts/check_dag.py
         - run: sudo apt-get install -y libgmp-dev
         - uses: leanprover/lean-action@v1
   ```

   The DAG check runs before the Lean build so import-boundary
   violations fail fast without spending build time. `lean-action`
   performs the `lake build` itself. `libgmp-dev` is installed
   explicitly because the `hex-arith` extern C shims `#include
   <gmp.h>`; Lean's toolchain ships `libgmp.a` for linking but not the
   headers, and `ubuntu-latest` does not preinstall `libgmp-dev`.

   **`.github/workflows/conformance.yml`** (optional, manual trigger):
   Manual or locally-triggered conformance workflow following
   `SPEC/testing.md`. Also uses `leanprover/lean-action` for the
   Lean portion of the build; external tools (Sage, FLINT, fpLLL)
   layer on top via `cachix/install-nix-action` when available. The
   full conformance workflow is not required for the minimal Phase 0
   repository bootstrap — a stub file pointing at `SPEC/testing.md`
   is sufficient at this stage.

7. Create `.gitignore` (at minimum: `.lake/`, `build/`).

8. Create a thin `README.md` pointing to `SPEC/SPEC.md`, `PLAN.md`,
   and `libraries.yml`.

9. Verify: `lake build` succeeds (trivially — empty files) and
   `python3 scripts/check_dag.py` exits 0.

## Exit criteria

Phase 0 is done when:

- `lean-toolchain` is the pinned baseline;
- `lakefile.toml` lists every library in `libraries.yml` (plus
  `HexManual`);
- `lake-manifest.json` pins Mathlib to the resolved tag for
  `v4.30.0-rc2`;
- every library has an empty-or-stub root `.lean` file and source
  directory, including `HexManual`;
- `scripts/check_dag.py` and `scripts/status.py` exist;
- both CI workflow files exist;
- `lake build` and `python3 scripts/check_dag.py` both succeed.

All `libraries.yml` entries remain at `done_through: 0` through Phase
0; the first per-library phase transition happens in Phase 1.
