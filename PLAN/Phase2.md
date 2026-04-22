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
