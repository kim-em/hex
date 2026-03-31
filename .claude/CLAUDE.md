# lean-algebra

Verified computational algebra in Lean 4, Mathlib-free.

## Key files

- **PLAN.md** — the canonical design document. All library descriptions,
  API surfaces, theorem statements, and vetted proof strategies live here.
  When proof research is complete and incorporated, the material belongs
  in PLAN.md under the relevant library section.

- **TRIAGE.md** — scratch space for proof research in progress. Items
  here are unvetted and may be incomplete. Once a proof strategy is
  understood, it gets incorporated into PLAN.md and deleted from
  TRIAGE.md. The goal is for TRIAGE.md to eventually be empty.

**Rule: no duplication between PLAN.md and TRIAGE.md.** Content lives
in exactly one place. If it's been incorporated into PLAN.md, delete
it from TRIAGE.md. Never create a "pointer" stub — just delete.

## Mathlib-free vs Mathlib split

Each library `lean-foo` has a potential companion `lean-foo-mathlib`.

- **`lean-foo`** (no Mathlib): algorithm implementations + correctness
  properties needed to define/state the computational interface.
  Proving your own GCD algorithm works is not "duplicating Mathlib."

- **`lean-foo-mathlib`** (with Mathlib): deeper correctness theorems
  that rely on abstract algebra Mathlib already provides (e.g.
  Euclidean domain theory, UFD, finite field theory). Uses ring
  equivalences to transfer results.

Don't rebuild abstract algebra that Mathlib provides. But anything
needed to define the computational interface stays in the Mathlib-free
library, even if it overlaps with Mathlib.

## Style

Don't add "research completed" timestamps, progress notes, or
meta-commentary about the history of our research process to any
file. The git history tracks that. PLAN.md and TRIAGE.md contain
the current state of the design, not a journal of how we got there.
