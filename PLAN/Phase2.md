# Phase 2: Scaffolding Review — "What Are We Missing?"

**Coupling:** local. Library L can start Phase 2 once
`libraries.yml[L].done_through ≥ 1`. Cross-library state is irrelevant.

After a library is scaffolded, create issues for **skeptical reviews**.
These are not rubber-stamp coverage audits — they ask:

> *What essential functionality is missing that downstream libraries
> will need?*

## Review questions

- Does hex-arith expose everything hex-mod-arith needs?
- Does hex-poly's `DensePoly` API support the operations hex-poly-fp
  requires?
- Are there lemmas about intermediate quantities that the SPEC doesn't
  mention but the proof strategies implicitly require?
- Are the theorem statements faithful to the SPEC? (Not "verbatim" — but
  do they capture the same mathematical content?)
- Are there missing imports or DAG violations?
- **Does every committed `def` / `structure` field / `class` /
  `instance` body actually implement the SPEC contract correctly?**
  [PLAN/Phase1.md](Phase1.md) forbids data-level placeholders of any
  kind — no `sorry` bodies, no `axiom`s standing in for data, no
  trivial returns (input unchanged, `0`, `Matrix.identity`, `none`,
  empty list). A library must commit only the declarations it can
  correctly implement; everything else stays out of Lean until a
  later PR implements it. Flag any committed declaration whose body
  is a placeholder in any of these forms. Flagged bodies must be
  deleted (and any downstream callers updated) in a follow-up issue
  before the `scaffolding-reviewed` token is committed — either the
  implementation becomes correct, or the declaration leaves the
  tree. "Rewrite as `sorry`" is **not** an acceptable fix.

## Output

GitHub issues flagging gaps. This may take multiple sessions per library.

## Exit criteria

For library `hex-foo`, Phase 2 is done when a reviewer *agent* (not
the author of the scaffolding) has read the scaffolded code against
`SPEC/Libraries/hex-foo.md`, opened follow-up issues for any gaps it
identifies, and committed a machine-checkable token file
`status/hex-foo.scaffolding-reviewed` recording that the review has
been performed.

Record completion by bumping `libraries.yml[L].done_through` to `2`.
The `status/hex-foo.scaffolding-reviewed` token is the separate
*point-in-time attestation* of the review; `libraries.yml` is the
mutable phase counter. Both are required at Phase 2 exit.
