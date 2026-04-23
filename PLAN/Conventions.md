# Conventions

Cross-phase conventions that apply across the entire project. Read
once per session.

---

## Hard rules

### SPEC immutability

**Do not modify files under `SPEC/`.** The only exception is the
"scope of autonomous SPEC edits" rule in `SPEC/design-principles.md`:
agents may fix SPEC clauses that are internally contradictory or
mathematically impossible, with rationale in the PR description.

### PR workflow

Every PR gets auto-merge at creation:

```bash
gh pr create --title "…" --body "…"
gh pr merge "$(gh pr view --json number --jq .number)" --auto --squash
```

At the start of every planner cycle, merge all mergeable+green open
PRs before creating new work. Downstream agents are blocked on `main`
until merged PRs land.

---

## Lexical conventions

### Naming

| Context | Convention | Example |
|---------|-----------|---------|
| SPEC library files | kebab-case | `hex-poly-z-mathlib.md` |
| Lean modules/dirs | PascalCase | `HexPolyZMathlib` |
| `libraries.yml` keys | PascalCase | `HexPolyZMathlib:` |
| `lakefile.toml` names | PascalCase | `name = "HexPolyZMathlib"` |

The PascalCase form is a direct transliteration of the kebab-case
name: each hyphen-separated segment becomes capitalised and joined
(`hex-poly-z-mathlib` → `HexPolyZMathlib`).

**Acronym exception.** Segments that are recognised acronyms keep
all their letters upper-case rather than capitalising only the first.
The current acronym list is:

| kebab segment | PascalCase form |
|---------------|-----------------|
| `gf2`         | `GF2`           |
| `lll`         | `LLL`           |
| `gfq`         | `GFq`           |
| `fp`          | `Fp`            |
| `crt`         | `CRT`           |

So `hex-gf2` → `HexGF2`, `hex-lll` → `HexLLL`, `hex-lll-mathlib`
→ `HexLLLMathlib`, `hex-gfq-field` → `HexGFqField`. (`gfq` is
"Galois field GF(q)" where `q = p^n` — the `q` is a variable, so
lower-case; `fp` is "F_p" with `p` variable, lower-case.)

Extend this table when adding libraries whose names involve further
acronyms. Do not silently introduce a mixed-case spelling.

> **Current state note (2026-04-23).** The existing modules
> `HexGf2` / `HexGf2Mathlib` / `HexLll` / `HexLllMathlib` in the
> repository predate this rule and still use the un-exceptioned
> transliteration. A global rename PR will align them with this
> convention; until that lands, agents must not rename these
> identifiers in isolation. New libraries should follow the acronym
> rule from the start.

### FFI

Libraries that use `@[extern]` (e.g. `hex-arith` for GMP wrappers,
`hex-gf2` for CLMUL) keep their C shims in a `ffi/` subdirectory
within the library (e.g. `HexArith/ffi/wide_arith.c`). The lakefile's
`moreLinkArgs` or `moreLeancArgs` fields connect them to the build.

---

## Issue creation

The project stays **GitHub-native** for orchestration. The canonical
task tracker is GitHub issues plus whatever structured fields GitHub
Projects or issue forms can provide. Do not introduce a separate
committed task-graph file that has to be kept in sync with issues.

Prefer the **issue body** over custom GitHub metadata unless there
is a clear need for the metadata. The issue body should contain the
canonical task description in a stable, easy-to-scan format.

### Narrow, not umbrella

- Use **many narrow issues** rather than a few large umbrella issues.
- Prefer issues scoped to one API surface, one proof cluster, one
  algorithmic subcomponent, or one benchmark/conformance target.
- Large umbrella issues are fine for human orientation, but
  execution should happen in smaller child or blocking issues.

Good issue sizes include:

- one major structure plus its immediate API;
- one SPEC subsection with a coherent implementation target;
- one theorem cluster that obviously belongs together;
- one conformance or benchmark slice for a single subsystem.

Avoid issues that mix:

- multiple libraries with weak coupling;
- implementation plus broad cleanup across unrelated files;
- an entire library's worth of declarations unless the library is tiny.

### Canonical issue body shape

Keep issue bodies simple Markdown, but standardize the section
headings so agents can read and write them consistently. Default
shape:

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

Keep these lines literal and easy to grep. They are the only
dependency syntax the orchestration layer should rely on by default.

### Decomposition is normal

If an agent is assigned an issue and concludes that it is too large
for one session, that is a normal outcome, not a failure.

Expected behavior:

- decompose the issue into smaller GitHub issues itself when it has
  enough context to do so well;
- link the new issues clearly as follow-up, blocking, or child work;
- add `depends-on: #N` lines where ordering matters;
- narrow the original issue if some subset is still tractable;
- if appropriate, stop after opening the smaller issues rather than
  attempting an oversized implementation.

Worker-created follow-up issues are encouraged when they improve
queue quality. Do not require a separate planning round-trip just
to split an issue that is clearly too large.

### Partial progress is valuable

Agents should not wait for total completion before contributing
useful work. Partial progress is encouraged when it leaves the
repository in a better state and makes follow-up work easier.

Good partial-progress outputs include:

- a PR that lands a coherent subset of the intended work;
- scaffolded declarations with correct boundaries and notes about
  what remains;
- proof skeletons or helper lemmas that unblock later work;
- benchmark or conformance harnesses without full coverage yet.

When an issue is only partially completed, the agent should
normally:

- open a PR for the finished subset if it is mergeable;
- open one or more follow-up issues for the remainder;
- record the new boundaries clearly so later agents can resume
  without re-discovering the decomposition.

---

## `libraries.yml` model

### Phase-dependency rule table

Notation: write `L.dt` for `libraries.yml[L].done_through`, `L.deps`
for L's direct dependencies. "Ready to start phase K" means all
prerequisites below are met.

| K | Name                       | Coupling    | Within-L prereq | Cross-lib prereq                   | Exit ⇒ set |
|---|----------------------------|-------------|-----------------|-------------------------------------|------------|
| 0 | Monorepo scaffolding       | global      | —               | —                                   | monorepo bootstrap lands on `main` |
| 1 | Library scaffolding        | dep-coupled | `L.dt ≥ 0`      | every `d ∈ L.deps: d.dt ≥ 1`        | `L.dt = 1` |
| 2 | Scaffolding review         | local       | `L.dt ≥ 1`      | —                                   | `L.dt = 2` |
| 3 | Conformance testing        | dep-coupled | `L.dt ≥ 2`      | every `d ∈ L.deps: d.dt ≥ 3`        | `L.dt = 3` |
| 4 | Performance & benchmarking | dep-coupled | `L.dt ≥ 3`      | every `d ∈ L.deps: d.dt ≥ 4`        | `L.dt = 4` |
| 5 | Implementation work loop   | local       | `L.dt ≥ 4`      | —                                   | `L.dt = 5` |
| 6 | Proof polishing            | local       | `L.dt ≥ 5`      | —                                   | `L.dt = 6` |
| 7 | User-facing documentation  | local       | `L.dt ≥ 6`      | —                                   | `L.dt = 7` |

This table is consumed mechanically by `scripts/status.py`. An agent
normally does not need to evaluate it by hand — run the script and
read its output.

### `done_through` semantics

- `done_through: K` means **phases 1..K are all complete** for L
  (linear, no skipping).
- `done_through: 0` is the seed state: no per-library phase is done,
  L is ready to start Phase 1 once the global Phase 0 bootstrap is
  complete.
- `done_through: 7` is fully done.
- Phase 0 is *global*, not per-library — its completion is observable
  via on-disk artifacts (`lakefile.toml`, `scripts/check_dag.py`,
  etc.), not via any `libraries.yml` field.
- "Dep-coupled" phases (1, 3, 4) require same-phase completion in
  every direct dep before L can start them. "Local" phases (2, 5,
  6, 7) require no cross-library gates.
- Strict linear: L cannot start Phase K before completing Phase K-1.
  `done_through` is an integer prefix, not an arbitrary set.
- Once deps reach `dep.dt ≥ 4`, the hardest cross-lib gate is
  satisfied and L can run through all subsequent local phases (5, 6,
  7) regardless of where deps go next.

### Where state lives

`libraries.yml` holds the mutable per-library phase counter plus
structural DAG data (`deps`, `mathlib`). Other state mechanisms:

- **GitHub issues** — the canonical work-item tracker; what is
  *being worked on right now*.
- **`status/hex-foo.<milestone>` tokens** — immutable point-in-time
  attestations (currently: `scaffolding-reviewed` for Phase 2
  sign-off). Complementary to `libraries.yml`, not subsumed by it.
- **`progress/` directory** — per-turn agent session notes (see
  [.claude/CLAUDE.md](../.claude/CLAUDE.md)).
- **`PLAN/` and `PLAN.md`** — reference material, not progress state.
  Do not modify them for progress tracking.
