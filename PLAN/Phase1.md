# Phase 1: Scaffolding

**Coupling:** dep-coupled. Library L can start Phase 1 once every
`d ∈ L.deps` has `libraries.yml[d].done_through ≥ 1`.

Create Lean files implementing each library's API as declared in the
SPEC. Parallelizable in DAG order (a library can be scaffolded once
its dependencies are scaffolded).

## What to scaffold

Read `SPEC/Libraries/hex-foo.md`. The SPEC contains explicit Lean
code blocks with `structure`, `def`, `theorem`, and `class`
declarations, and some newer library specs also give explicit API
contracts in prose with named suggested declarations. These stable
declarations and record shapes are the scaffolding targets. Prose
discussion of proof strategies, alternatives, heuristics, and
examples is context for later phases, not a scaffolding obligation,
unless it explicitly fixes the public API or theorem split.

## Rules

- **Real definitions, no definition-level sorry.** Every `structure`,
  `def`, `class`, and `instance` must have a real implementation.
  Data must be constructed. Propositional obligations (theorem
  proofs, proof fields within structures) should use `sorry`.

- **`sorry`'d theorem proofs are expected.** The point of scaffolding
  is to get the API surface compiling, not to fill in proofs.

- **Helper definitions** not in the SPEC are fine if needed to state
  the API. Note them in the PR.

- **Verify:** `lake build` must succeed after each scaffolding PR.

## Work unit granularity (Phase 1)

Phase 1 issues are typically one-per-major-structure or
one-per-SPEC-subsection — whichever matches the shape of the SPEC
file. A single structure definition plus its basic API lemmas is
often the right size. Every library will need many PRs across many
agent sessions.

General issue-writing conventions (narrow issues, canonical body
shape, decomposition, partial progress) live in
[Conventions.md](Conventions.md).

## Exit criteria

For library `hex-foo`, Phase 1 is done when:

- every named `def`, `structure`, `class`, `instance`, and `theorem`
  in `SPEC/Libraries/hex-foo.md` has a matching Lean declaration
  with the SPEC's signature;
- `lake build <HexFooLib>` succeeds (proofs may be `sorry`;
  data-level declarations must not be);
- each new `.lean` file carries a module docstring summarising the
  library contents;
- no `TODO`, `FIXME`, or `...` placeholder remains in the scaffolded
  code (other than `sorry` in proofs).

Record completion by bumping `libraries.yml[L].done_through` to `1`.
