# hex

Verified computational algebra in Lean 4, Mathlib-free.

## Key files

- **SPEC/** — the canonical design document, split into focused files.
  `SPEC/SPEC.md` is the entry point. Per-library specs live in
  `SPEC/Libraries/hex-*.md`. All API surfaces, theorem statements,
  and vetted proof strategies live here.

- **PLAN.md** — workflow document describing how agents/humans execute
  the SPEC. Phases: monorepo scaffolding, library scaffolding,
  scaffolding review, conformance testing, implementation, polishing.

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
