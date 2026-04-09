# hex — Workflow Plan

This document describes **how** to execute the spec in `SPEC/`. Work through
the phases in order. Use GitHub issues to track progress. Do not modify
this file for progress tracking.

The spec (`SPEC/SPEC.md` and linked files) describes **what** to build.
This document describes the pipeline for building it.

---

## Phase 0: Monorepo Scaffolding

One-time setup. Create the Lake monorepo infrastructure by reading the
spec and this document.

### Steps

1. Create `lean-toolchain` pinning the current stable Lean 4 release.

2. Create `lakefile.toml` with one `[[lean_lib]]` per library in the DAG
   (see `SPEC/Libraries/README.md` for the full list). Pin Mathlib to a
   specific commit (not `master`). Each library entry needs:
   - `name` — PascalCase (e.g. `HexArith`, `HexPolyZMathlib`)
   - `srcDir = "."`
   - `roots` — matching the PascalCase name
   - Mathlib bridge libraries should declare `needs = ["mathlib"]`

3. Create empty root files and source directories for every library:
   - `HexArith.lean` (empty or minimal) + `HexArith/` directory
   - `HexPoly.lean` + `HexPoly/`
   - ... (one pair per library in the DAG)
   - `HexModArithMathlib.lean` + `HexModArithMathlib/`
   - ... (one pair per mathlib bridge)

4. Write `scripts/dag.json` — the single canonical source of truth for
   the project DAG. Format:

   ```json
   {
     "libraries": {
       "HexArith": { "deps": [], "mathlib": false },
       "HexPoly": { "deps": [], "mathlib": false },
       "HexModArith": { "deps": ["HexArith"], "mathlib": false },
       "HexModArithMathlib": { "deps": ["HexModArith"], "mathlib": true },
       ...
     }
   }
   ```

   - PascalCase library names matching the `[[lean_lib]]` entries.
   - `deps`: direct dependencies (other libraries in this repo).
   - `mathlib`: `true` only for `-mathlib` bridge libraries.
   - The full DAG is in `SPEC/Libraries/README.md`.

5. Write `scripts/check_dag.py` — a Python script (~120 lines) that
   enforces the DAG. It should:

   **Structural checks:**
   - Verify the graph is acyclic (topological sort succeeds).
   - Every dependency in `dag.json` names an existing library.
   - Every `dag.json` library has a matching `[[lean_lib]]` in
     `lakefile.toml` (parse TOML via `tomllib`, stdlib since 3.11).
   - Every `[[lean_lib]]` has a matching `dag.json` entry.
   - Every library's root `.lean` file exists on disk.

   **Import boundary checks:**
   - For each `.lean` file (excluding `.lake/`), determine its library
     from the file path (top-level directory or root file name).
   - For each `import` statement, verify the imported module belongs to
     the same library, a declared dependency, or stdlib/core.
   - If the import starts with `Mathlib`, verify the library has
     `"mathlib": true` in `dag.json`.
   - Exit non-zero on any violation, printing all violations to stderr.

6. Set up CI:

   **`.github/workflows/ci.yml`** (required, runs on every push/PR):
   ```yaml
   name: CI
   on: [push, pull_request]
   jobs:
     build:
       runs-on: ubuntu-latest
       steps:
         - uses: actions/checkout@v4
         - uses: leanprover/lean-action@v1
         - run: python3 scripts/check_dag.py
         - run: lake build
   ```

   **`.github/workflows/conformance.yml`** (optional, manual trigger):
   Placeholder for conformance testing against FLINT/SageMath. Details
   TBD in Phase 3 planning.

7. Create `.gitignore` (at minimum: `.lake/`, `build/`).

8. Create a thin `README.md` pointing to `SPEC/SPEC.md` and `PLAN.md`.

9. Verify: `lake build` succeeds (trivially — empty files) and
   `python3 scripts/check_dag.py` exits 0.

### FFI convention

Libraries that use `@[extern]` (e.g. hex-arith for GMP wrappers,
hex-gf2 for CLMUL) keep their C shims in a `ffi/` subdirectory
within the library (e.g. `HexArith/ffi/wide_arith.c`). The lakefile's
`moreLinkArgs` or `moreLeancArgs` fields connect them to the build.

### Naming conventions

| Context | Convention | Example |
|---------|-----------|---------|
| SPEC library files | kebab-case | `hex-poly-z-mathlib.md` |
| Lean modules/dirs | PascalCase | `HexPolyZMathlib` |
| `dag.json` keys | PascalCase | `"HexPolyZMathlib"` |
| `lakefile.toml` names | PascalCase | `name = "HexPolyZMathlib"` |

---

## Phase 1: Scaffolding

Create Lean files implementing each library's API as declared in the
SPEC. Parallelizable in DAG order (a library can be scaffolded once its
dependencies are scaffolded).

### What to scaffold

Read `SPEC/Libraries/hex-foo.md`. The SPEC contains explicit Lean code
blocks with `structure`, `def`, `theorem`, and `class` declarations —
these are the scaffolding targets. Prose discussion of proof strategies,
alternatives, and examples is context for later phases, not a scaffolding
obligation.

### Rules

- **Real definitions, no definition-level sorry.** Every `structure`,
  `def`, `class`, and `instance` must have a real implementation. Data
  must be constructed. Only propositional obligations (theorem proofs,
  proof fields within structures) may use `sorry`.

- **`sorry`'d theorem proofs are expected.** The point of scaffolding is
  to get the API surface compiling, not to fill in proofs.

- **Helper definitions** not in the SPEC are fine if needed to state the
  API. Note them in the PR.

- **Verify:** `lake build` must succeed after each scaffolding PR.

### Work unit granularity

Work units are **dynamic**, not one-per-library. The orchestrating agent
decides how to decompose based on SPEC complexity:

- A small library (hex-conway, hex-gfq) might be one work unit.
- A large library (hex-lll with LLLState, integrality, termination;
  hex-arith with Barrett, Montgomery, extGcd, Fermat) should be broken
  into multiple work units.
- Guidance: one work unit per major `structure` or API surface in the
  SPEC, or per SPEC subsection if the file has clear subsections.
- Each work unit is a GitHub issue + PR with auto-merge enabled.

---

## Phase 2: Scaffolding Review — "What Are We Missing?"

After a library is scaffolded, create issues for **skeptical reviews**.
These are not rubber-stamp coverage audits — they ask:

> *What essential functionality is missing that downstream libraries
> will need?*

### Review questions

- Does hex-arith expose everything hex-mod-arith needs?
- Does hex-poly's `DensePoly` API support the operations hex-poly-fp
  requires?
- Are there lemmas about intermediate quantities that the SPEC doesn't
  mention but the proof strategies implicitly require?
- Are the theorem statements faithful to the SPEC? (Not "verbatim" — but
  do they capture the same mathematical content?)
- Are there missing imports or DAG violations?

### Output

GitHub issues flagging gaps, with proposed additions to the SPEC or
directly to the scaffold. This may take multiple sessions per library.

---

## Phase 3: Conformance Testing

Conformance testing comes **before** proofs. No point proving theorems
about wrong implementations.

> **TODO: This phase needs its own planning session.** The questions
> below must be answered before agents can execute Phase 3.

### Open questions

- **What can be tested for each library?** Not all libraries have obvious
  external oracles. hex-arith (extGcd, Barrett, Montgomery) and hex-poly
  (polynomial arithmetic) are straightforward; hex-lll is testable
  against fpLLL; hex-berlekamp against FLINT. What about hex-hensel,
  hex-gram-schmidt, hex-gfq-*?

- **Test harness shape.** Lean `#eval` producing output compared against
  reference files? FFI bridge to FLINT for direct comparison? SageMath
  scripts generating test vectors committed as fixtures?

- **Infrastructure.** FLINT/SageMath are not available on stock
  `ubuntu-latest`. Options: containerized CI job, manual/scheduled
  workflow, local-only validation with committed fixtures.

- **Seeds, reproducibility, failure replay.** Deterministic seeds for
  random test generation. How to minimize/replay failures.

---

## Phase 4: Implementation Work Loop

Fill in `sorry`'d proofs. One GitHub issue per theorem or small group
of related theorems.

### Task selection

In priority order:
1. Items that unblock the most downstream work (high fan-out in the DAG).
2. Items assessed as mathematically hardest (from Phase 2 review or
   periodic status checks).
3. Items with the most `sorry`s in a single file.

### Workflow

- **Work top-down.** Replace `sorry` with structured proof skeletons
  (tactic blocks with intermediate `sorry`s) before filling in helper
  lemmas. This reveals the proof structure early.

- **Push sorries earlier.** If theorem A uses lemma B, and B is `sorry`,
  that's fine — work on A's proof structure anyway. Lean treats `sorry`
  as an axiom; downstream proofs compile.

- **PRs with auto-merge** enabled where CI is passing.

- **Periodic status checks** (every ~50 merged PRs or at natural
  milestones): regression check for definition-level sorries, identify
  hardest remaining items, flag neglected libraries.

---

## Phase 5: Proof Polishing

Bring sorry-free proofs to Mathlib quality. This is substantially more
than mechanical cleanup.

### What Mathlib quality means

- **Good API design.** Right level of generality; clean theorem
  statements that are easy to apply downstream.
- **Encapsulation via characterising lemmas.** Don't force users to
  unfold definitions; provide the lemmas that characterise each
  definition's behavior.
- **Avoiding defeq abuse.** Don't rely on definitional equality for
  things that should be stated as lemmas.
- **Appropriate automation annotations.** `@[simp]` lemmas for
  normalization, `@[grind]` for automated reasoning. Maximize what
  `simp` and `grind` can close automatically.
- **Clean imports and namespace management.** Minimal imports, proper
  `open` scoping, no namespace pollution.

> **TODO: Link to resources.** This phase needs concrete guidance
> documents referenced here:
> - Mathlib contribution standards
> - Mathlib API design guidelines
> - The `mathlib4` style guide
> - Examples of good API design in Mathlib (e.g. `Finset`, `Polynomial`)

---

## Progress Tracking

- **GitHub issues** are the canonical work-item tracker. One issue per
  scaffolding work unit; one issue per theorem or small group for
  implementation.
- **This file (PLAN.md) is the reference plan.** Do not modify it for
  progress tracking.
- **Auto-merge PRs** where CI is passing. Batch-merge mergeable PRs at
  the start of each planning cycle.
