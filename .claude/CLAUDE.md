# hex

Verified computational algebra in Lean 4, Mathlib-free.

## Key files

- **SPEC/** — the canonical design document, split into focused files.
  `SPEC/SPEC.md` is the entry point. Per-library specs live in
  `SPEC/Libraries/hex-*.md`. All API surfaces, theorem statements,
  and vetted proof strategies live here.

- **PLAN.md** — workflow document describing how agents/humans execute
  the SPEC. Phases: monorepo scaffolding, library scaffolding,
  scaffolding review, conformance testing, performance and
  benchmarking, implementation, polishing.

**Rule: no duplication between SPEC files.** Content lives in exactly
one place. If material is moved between files, delete the original.

## Mathlib-free vs Mathlib split

Each library `hex-foo` has a potential companion `hex-foo-mathlib`.

- **`hex-foo`** (no Mathlib): algorithm implementations + correctness
  properties needed to define/state the computational interface.
  Proving your own GCD algorithm works is not "duplicating Mathlib."

- **`hex-foo-mathlib`** (with Mathlib): deeper correctness theorems
  that rely on abstract algebra Mathlib already provides (e.g.
  Euclidean domain theory, UFD, finite field theory). Uses ring
  equivalences to transfer results.

Don't rebuild abstract algebra that Mathlib provides. But anything
needed to define the computational interface stays in the Mathlib-free
library, even if it overlaps with Mathlib.

## Style

Don't add "research completed" timestamps, progress notes, or
meta-commentary about the history of our research process to any
file. The git history tracks that. SPEC files and PLAN.md contain
the current state of the design, not a journal of how we got there.

## Per-turn progress files

Start of turn: read the most recent file in `progress/` (ISO-8601
timestamps sort chronologically). If only `progress/0000-init.md`
exists, the repo is freshly initialised — proceed with Phase 0.

End of turn: write `progress/<UTC-timestamp>.md` with sections
Accomplished / Current frontier / Overall project progress / Next
step / Blockers. Commits made during the turn should mention the
progress file.

## Quality metrics

Planners record per cycle:

- per-library sorry counts, split into **definition-level** (must be
  0) and **proof-level** (counts are fine);
- `lake build` and `scripts/check_dag.py` status;
- conformance profile status (`core` / `ci` / `local`) per library;
- presence of `status/hex-foo.scaffolding-reviewed` tokens.

## PR workflow

Every PR gets auto-merge at creation:

```bash
gh pr create --title "…" --body "…"
gh pr merge "$(gh pr view --json number --jq .number)" --auto --squash
```

At the start of every planner cycle, merge all mergeable+green open
PRs before creating new work. Downstream agents are blocked on `main`
until merged PRs land.

## Lean

Check diagnostics after every step; don't continue past errors. Build
via `lake build`, not `lean` directly. `native_decide` is banned (see
SPEC).
