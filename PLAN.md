# hex — Workflow Plan

This document describes **how** to execute the spec in `SPEC/`. Work through
the phases in order. Use GitHub issues to track progress. Do not modify
this file for progress tracking.

The spec (`SPEC/SPEC.md` and linked files) describes **what** to build.
This document describes the pipeline for building it.

**Do not modify files under `SPEC/`.** The SPEC is a fixed design
document, not a working surface. The only exception is the narrow
"scope of autonomous SPEC edits" rule in `SPEC/design-principles.md`:
agents may edit a SPEC clause that is ill-typed, internally
contradictory, or clearly mathematically impossible, with the
rationale in the PR description. Release churn, benchmark tweaks,
refactoring preferences, and "I would have written it differently"
are **not** grounds for SPEC edits. When in doubt, leave `SPEC/`
alone and record the change elsewhere (PR description, issue, release
notes).

## Release Targets

Think about release targets in terms of **verified finite fields**, not
just the Berlekamp-Zassenhaus capstone in isolation.

Separate two different milestones:

- the **constructor layer**, where users can define quotient rings and
  finite fields provided they already have an irreducibility proof;
- the **evidence-producing layer**, where this project can generate or
  check the irreducibility evidence natively in Lean.

Berlekamp-Zassenhaus is not needed for the basic `GF(p^n)` constructor
story over `F_p`. That evidence comes from Berlekamp/Rabin over finite
fields. Berlekamp-Zassenhaus matters later for irreducibility and
factoring workflows over `Z[x]`, and for downstream number-theory uses
that start from integer polynomials.

### Release ladder

1. **Finite-field constructor release.**
   - `hex-mod-arith`, `hex-poly`, `hex-poly-fp`, `hex-gfq-ring`,
     `hex-gfq-field`, `hex-gf2`
   - Users can construct quotient rings and finite fields in Lean from a
     user-supplied irreducibility proof.
   - This release does **not** claim that the project can yet generate
     irreducibility evidence on demand.

2. **Irreducibility engine release.**
   - `hex-berlekamp`, `hex-berlekamp-mathlib`, `hex-conway`, `hex-gfq`
   - Users can natively generate or check that irreducibility proof over
     `F_p` and use it to instantiate `FiniteField p f hf hirr`.
   - This is the first release where on-demand `GF(p^n)` construction is
     fully credible inside the project itself.

3. **Integer factoring support release.**
   - `hex-poly-z`, `hex-hensel`, `hex-berlekamp-zassenhaus`
   - Berlekamp-Zassenhaus supports irreducibility and factoring
     workflows that start from integer polynomials, and replaces
     external CAS dependencies in downstream number-theory projects.

4. **Polynomial-time capstone release.**
   - `hex-lll` integrated into `hex-berlekamp-zassenhaus`
   - The full polynomial-time Berlekamp-Zassenhaus pipeline is available,
     and finite-field/irreducibility workflows no longer depend on the
     exponential recombination fallback.

### Release criteria

For any release target above:

- The required libraries build together in CI.
- There is at least one end-to-end example exercising the advertised
  user story.
- The relevant computational path runs natively in Lean.
- Any irreducibility or field-construction claim exposed by the release
  is backed by Lean-checked evidence, not by an external oracle.

### User-facing artifacts

User-facing documentation is a **final-stage release artifact**, not a
driver of early scaffolding or proof scheduling.

- The project should eventually ship a small Verso tutorial site
  published to GitHub Pages.
- Those tutorials should be downstream of the corresponding library
  releases and should not block core algorithm development.
- The concrete tutorial set is specified in `SPEC/tutorials.md`.

---

## Phase 0: Monorepo Scaffolding

One-time setup. Create the Lake monorepo infrastructure by reading the
spec and this document.

The repository begins markdown-only (`SPEC/`, `PLAN.md`, `AGENTS.md`,
`.claude/CLAUDE.md`). Phase 0 is responsible for creating every
non-markdown file in the repository. Treat it as a single
`--critical-path` feature issue handled by one worker; do not fan out
into Phase 1 until the Phase 0 PR lands on `main`.

### Steps

1. Create `lean-toolchain` containing exactly
   `leanprover/lean4:v4.30.0-rc2`. This is the project baseline; do
   not substitute a different release. 

2. Create `lakefile.toml` with one `[[lean_lib]]` per library in the DAG
   (see `SPEC/Libraries/README.md` for the full list). All `-mathlib`
   bridge libraries depend on the Mathlib tag `v4.30.0-rc2`.
   Each library entry needs:
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

8. Create a thin `README.md` pointing to `SPEC/SPEC.md` and `PLAN.md`.

9. Verify: `lake build` succeeds (trivially — empty files) and
   `python3 scripts/check_dag.py` exits 0.

### Exit criteria

Phase 0 is done when: `lean-toolchain` is the pinned baseline,
`lakefile.toml` lists every library in the DAG, `lake-manifest.json`
pins Mathlib to the resolved tag for `v4.30.0-rc2`, every library has
an empty-or-stub root `.lean` file and source directory, `scripts/
dag.json` and `scripts/check_dag.py` exist, the two CI workflow files
exist, and `lake build` and `python3 scripts/check_dag.py` both
succeed.

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
blocks with `structure`, `def`, `theorem`, and `class` declarations, and
some newer library specs also give explicit API contracts in prose with
named suggested declarations. These stable declarations and record
shapes are the scaffolding targets. Prose discussion of proof
strategies, alternatives, heuristics, and examples is context for later
phases, not a scaffolding obligation, unless it explicitly fixes the
public API or theorem split.

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

- A single structure definition and its basic API lemmas might be one
  work unit. Every library will need many PRs/agent sessions.
- Guidance: one work unit per major `structure` or API surface in the
  SPEC, or per SPEC subsection if the file has clear subsections.
- Each work unit is a GitHub issue + PR with auto-merge enabled.

### GitHub-Centric Work Tracking

The project should stay **GitHub-native** for orchestration. The
canonical task tracker is GitHub issues plus whatever structured fields
GitHub Projects or issue forms can provide. Do not introduce a separate
committed task-graph file that has to be kept in sync with issues.

Prefer the **issue body** over custom GitHub metadata unless there is a
clear need for the metadata. The issue body should contain the canonical
task description in a stable, easy-to-scan format.

Suggested shape:

- Use **many narrow issues** rather than a few large umbrella issues.
- Prefer issues scoped to one API surface, one proof cluster, one
  algorithmic subcomponent, or one benchmark/conformance target.
- Large umbrella issues are fine for human orientation, but execution
  should happen in smaller child or blocking issues.

Good issue sizes include:

- one major structure plus its immediate API;
- one SPEC subsection with a coherent implementation target;
- one theorem cluster that obviously belongs together;
- one conformance or benchmark slice for a single subsystem.

Avoid issues that mix:

- multiple libraries with weak coupling;
- implementation plus broad cleanup across unrelated files;
- an entire library's worth of declarations unless the library is tiny.

### Canonical Issue Body Shape

Keep issue bodies simple Markdown, but standardize the section headings
so agents can read and write them consistently. A good default shape is:

- **Current state** — what is already true, and what assumptions the
  worker should begin from.
- **Deliverables** — the concrete outputs expected from this issue.
- **Context** — links to SPEC sections, files, related issues, or PRs.
- **Verification** — the checks to run for this issue.
- **Out of scope** — nearby work that should not be folded into this
  issue.

For hard blockers, include explicit dependency lines in the body:

```text
depends-on: #123
depends-on: #124
```

Keep these lines literal and easy to grep. They are the only dependency
syntax the orchestration layer should rely on by default.

### Decomposition Is Normal

If an agent is assigned an issue and concludes that it is too large for
one session, that is a normal outcome, not a failure.

Expected behavior:

- decompose the issue into smaller GitHub issues itself when it has
  enough context to do so well;
- link the new issues clearly as follow-up, blocking, or child work;
- add `depends-on: #N` lines where ordering matters;
- narrow the original issue if some subset is still tractable;
- if appropriate, stop after opening the smaller issues rather than
  attempting an oversized implementation.

Worker-created follow-up issues are encouraged when they improve queue
quality. Do not require a separate planning round-trip just to split an
issue that is clearly too large.

### Partial Progress Is Valuable

Agents should not wait for total completion before contributing useful
work. Partial progress is encouraged when it leaves the repository in a
better state and makes follow-up work easier.

Good partial-progress outputs include:

- a PR that lands a coherent subset of the intended work;
- scaffolded declarations with correct boundaries and notes about what
  remains;
- proof skeletons or helper lemmas that unblock later work;
- benchmark or conformance harnesses without full coverage yet.

When an issue is only partially completed, the agent should normally:

- open a PR for the finished subset if it is mergeable;
- open one or more follow-up issues for the remainder;
- record the new boundaries clearly so later agents can resume without
  re-discovering the decomposition.

### Exit criteria

For library `hex-foo`, Phase 1 is done when:

- every named `def`, `structure`, `class`, `instance`, and `theorem`
  in `SPEC/Libraries/hex-foo.md` has a matching Lean declaration with
  the SPEC's signature;
- `lake build <HexFooLib>` succeeds (proofs may be `sorry`; data-level
  declarations must not be);
- each new `.lean` file carries a module docstring summarising the
  library contents;
- no `TODO`, `FIXME`, or `...` placeholder remains in the scaffolded
  code (other than `sorry` in proofs).

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

GitHub issues flagging gaps. This may take multiple sessions per library.

### Exit criteria

For library `hex-foo`, Phase 2 is done when a reviewer *agent* (not
the author of the scaffolding) has read the scaffolded code against
`SPEC/Libraries/hex-foo.md`, opened follow-up issues for any gaps it
identifies, and committed a machine-checkable token file
`status/hex-foo.scaffolding-reviewed` recording that the review has
been performed. 

---

## Phase 3: Conformance Testing

Conformance testing comes **before** proofs. No point proving theorems
about wrong implementations.

Phase 3 should follow `SPEC/testing.md`. In particular:

- Use the three testing profiles:
  - `core` — deterministic Lean-only checks with no external tools
  - `ci` — modest randomized cross-checks using external tools only when
    available
  - `local` — larger or manually triggered campaigns
- Treat failures as replayable artifacts. Record at least the library,
  profile, seed, and serialized input case.
- Keep execution-mode distinctions explicit:
  - `always`
  - `if_available`
  - `required`

### Oracle guidance

- `hex-arith`, `hex-mod-arith`: Lean built-in big integer semantics
- `hex-poly`, `hex-poly-z`, `hex-poly-fp`: FLINT or Sage polynomial
  arithmetic; `python-flint` is a useful partial oracle
- `hex-matrix`, `hex-gram-schmidt`: Sage exact matrix / rational linear
  algebra
- `hex-gf2`, `hex-gfq-ring`, `hex-gfq-field`, `hex-gfq`: Sage finite
  field and quotient-ring computations
- `hex-berlekamp`, `hex-berlekamp-zassenhaus`: FLINT or Sage
  factorization / irreducibility checks
- `hex-hensel`: Sage or FLINT Hensel lifting, plus direct congruence and
  product checks
- `hex-lll`: fpLLL or Sage `LLL`, comparing reducedness and lattice
  equality rather than exact basis equality
- `hex-conway`: committed fixtures cross-checked against Sage's Conway
  tables

### Infrastructure guidance

- Prefer JSON or JSONL for serialized test cases and normalized oracle
  outputs.
- Lean produces and consumes the shared case format; Python or shell
  drivers handle tool detection and oracle invocation.
- Sage should not rely on Ubuntu `apt` packages in CI. Prefer a
  Nix-based Sage path (`nix shell nixpkgs#sage ...`) for local and CI
  parity. `cachix/install-nix-action` is the expected GitHub Actions
  installation path when Sage-backed CI jobs are added.
- Keep standard CI small enough for hosted runners and partial tool
  availability; reserve larger runs for `local` or manual jobs.

### Exit criteria

Phase 3 is done for a library when, for each of the `core`/`ci`/
`local` profiles in `SPEC/testing.md`:

- the library has named fixtures committed to the repository;
- the property-test runner passes on the default seed recorded with
  the fixture metadata;
- there is at least one end-to-end case exercising every advertised
  user story in the library's release target (see "Release ladder"
  above).

CI for the `core` and `ci` profiles must be green on the conformance
workflow before a library leaves Phase 3.

---

## Phase 4: Performance and Benchmarking

Performance is part of the project spec, not an optional cleanup task.
Before calling a release target successful, measure the cost of the
native Lean implementations on representative workloads.

### Goals

- Catch major performance regressions early.
- Validate that specialized code paths (`UInt64`, Barrett/Montgomery,
  packed GF(2), d-representation LLL) are actually paying for their
  complexity.
- Keep the finite-field-oriented releases honest: field construction and
  irreducibility checking must be usable, not merely correct on paper.

### Scope

- **hex-mod-arith:** modular multiply, inverse, exponentiation.
- **hex-poly / hex-poly-fp:** multiply, div/mod, GCD, Frobenius powers.
- **hex-gf2:** packed multiply, modular reduction, GCD, `GF(2^n)` ops.
- **hex-berlekamp:** Berlekamp matrix construction, nullspace, factor
  splits, Rabin test.
- **hex-hensel:** linear lifting baseline; quadratic lifting once added.
- **hex-lll:** size reduction, swap-heavy cases, full reduction.
- **hex-gfq / hex-gfq-field:** field multiplication/inversion for
  representative `(p, n)` pairs.
- **hex-berlekamp-zassenhaus:** end-to-end factoring on small and
  medium examples, with and without LLL where both paths exist.

### Benchmark discipline

- Maintain a small committed benchmark suite with fixed seeds and named
  inputs so regressions are reproducible.
- Benchmark both micro-kernels and end-to-end workflows.
- Track at least relative comparisons where they matter:
  - `GF2Poly` vs `FpPoly 2`
  - Barrett vs Montgomery crossover regimes
  - linear vs quadratic Hensel lifting
  - exponential recombination vs LLL-assisted recombination
- Keep benchmarking separate from proof obligations: benchmark the
  executable code path actually used at runtime.

### Release expectations

- Each release target must name the benchmark cases it must pass.
- Specific cases and thresholds may evolve between releases, but every
  such change must be accompanied by a short rationale in the PR that
  changes the benchmark set (one paragraph per change). This keeps the
  release gate machine-checkable without freezing the case list, and
  keeps release-specific churn out of `SPEC/`.
- A release is blocked by obvious performance pathologies even if proofs
  are complete.
- Record benchmark results in PRs or milestone notes so the orchestrator
  can detect regressions over time.

---

## Phase 5: Implementation Work Loop

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

- **Push sorries earlier.** When a proof is hard, replace it with a proof outline
  that cites new, clearly-stated lemmas (which may themselves be
  `sorry`) one level closer to the foundations. See
  `SPEC/design-principles.md` for the authoritative statement of the
  idiom. 

- **PRs with auto-merge** enabled where CI is passing.

- **Periodic status checks** (every ~50 merged PRs or at natural
  milestones): regression check for definition-level sorries, identify
  hardest remaining items, flag neglected libraries.

### Exit criteria

For library `hex-foo`, Phase 5 is done when it has zero `sorry`
occurrences (counted across all declarations, not just top-level
theorems), `lake build` is green on the pinned toolchain, and the
Phase 3 conformance suite for the library still passes.

---

## Phase 6: Proof Polishing

Bring sorry-free proofs to Mathlib quality. This is substantially more
than mechanical cleanup.

### Granularity

Every non-trivial definition or theorem needs separate treatment here.
This is not a "run a linter and clean up" pass — it requires careful
thought about API design for each declaration.

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
- **Follow Mathlib's published local standards.** In particular:
  - contribution guide:
    <https://leanprover-community.github.io/contribute/index.html>
  - style guide:
    <https://leanprover-community.github.io/contribute/style.html>
  - naming conventions:
    <https://leanprover-community.github.io/contribute/naming.html>
  - documentation style:
    <https://leanprover-community.github.io/contribute/doc.html>

This project is not committing to upstreaming as part of the plan; the
point of these references is to set a local quality bar for bridge
libraries and proof-heavy cleanup.

### Exit criteria

For library `hex-foo`, Phase 6 is done when:

- the Mathlib linter is clean on the library;
- docstring coverage meets the rule in `SPEC/design-principles.md`
  (public declarations and non-obvious private helpers);
- the library contains no dead or unreferenced declarations;
- the library passes a performance regression check against the
  previous tagged benchmark baseline if one exists, otherwise
  against the most recent committed benchmark baseline (the
  bootstrap case before any release has been tagged).

---

## Progress Tracking

- **GitHub issues** are the canonical work-item tracker. One issue per
  scaffolding work unit; one issue per theorem or small group for
  implementation.
- **This file (PLAN.md) is the reference plan.** Do not modify it for
  progress tracking.
- **Auto-merge PRs** where CI is passing. Batch-merge mergeable PRs at
  the start of each planning cycle.
