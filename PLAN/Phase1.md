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

- **Correct implementations, or honest placeholders — no middle
  ground.** Every `def`, `structure` field, `class`, and `instance`
  must have a body that either
  (a) *correctly* implements the SPEC contract for that declaration,
  or
  (b) is `sorry` (making the declaration `noncomputable`, trapping
  at runtime via `sorryAx`, and leaving a visible warning).
  **Placeholder bodies that typecheck but return wrong-but-plausible
  output are forbidden** — they lie to downstream callers and invite
  scaffold-locking conformance tests that pretend the stub is right.

  Examples of forbidden bodies, each observed in practice:
  - `def rref M := { rank := 0, echelon := M, transform := 1 }`
    — the name promises RREF; the body is not RREF.
  - `def spanCoeffs _ _ := none` — promises a span decomposition;
    always says "no".
  - `def gramSchmidt.basis b := b` — promises orthogonalisation;
    returns input unchanged.
  - `def gramSchmidt.coeffs _ := Matrix.identity` — promises the
    lower-triangular Gram-Schmidt coefficient matrix; returns the
    identity.

  If you cannot implement a function correctly in this PR, either
  defer the declaration entirely (if nothing downstream needs the
  signature yet) or write the signature with a `sorry` body:

  ```lean
  noncomputable def rref (M : Matrix Rat n m) : RrefResult n m := sorry
  ```

  The next agent picking it up sees the `sorry` and knows there's
  real work to do. A plausible-looking lie is invisible to both the
  next agent and to conformance tests.

- **`sorry`'d theorem proofs are expected.** The point of scaffolding
  is to get the API surface compiling, not to fill in proofs. This
  rule applies to `theorem` bodies and propositional `structure`
  fields. It does **not** extend an escape valve for data-level
  bodies — see the rule above.

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
- `lake build <HexFooLib>` succeeds (proofs may be `sorry`; data-level
  declarations are either correct implementations or `sorry`-bodied
  noncomputable stubs — wrong-but-plausible bodies are forbidden);
- each new `.lean` file carries a module docstring summarising the
  library contents;
- no `TODO`, `FIXME`, or `...` placeholder remains in the scaffolded
  code (other than `sorry` in proofs).

Record completion by bumping `libraries.yml[L].done_through` to `1`.
