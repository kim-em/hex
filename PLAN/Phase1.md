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

- **No data-level placeholders — at all.** Every `def`, `structure`
  field, `class`, and `instance` must have a body that *correctly*
  implements the SPEC contract for that declaration. There is no
  placeholder form that's acceptable: not wrong-but-plausible bodies
  (`def rref M := { rank := 0, echelon := M, transform := 1 }`),
  not `sorry` bodies (`noncomputable def rref ... := sorry`), not
  `axiom rref : ...`, not trivial returns (`Matrix.identity`, `none`,
  the input unchanged). If you cannot implement it correctly in this
  PR, **do not commit the declaration** — leave it out of Lean
  entirely. The SPEC file is the record of what's designed; the Lean
  surface is the record of what's implemented correctly so far.

  Why: a placeholder that typechecks lies to downstream code and to
  future agents. A wrong-but-plausible body invites scaffold-locking
  conformance tests. A `sorry` body makes every caller's `#eval`
  refuse to run (Lean conservatively refuses any term transitively
  depending on `sorry`), so any conformance test against that caller
  has to use `#eval!`, which then silently accepts whatever bits the
  runtime produces for `sorryAx` — neither "correct" nor "obviously
  wrong", just untrustworthy. An omitted declaration, by contrast,
  breaks the build at the use site loudly and points the next agent
  directly at the thing to implement.

  Forbidden data-level body patterns, each observed in practice:
  - `def rref M := { rank := 0, echelon := M, transform := 1 }`
    — the name promises RREF; the body is not RREF.
  - `def spanCoeffs _ _ := none` — promises a span decomposition;
    always says "no".
  - `def gramSchmidt.basis b := b` — promises orthogonalisation;
    returns input unchanged.
  - `def gramSchmidt.coeffs _ := Matrix.identity` — promises the
    lower-triangular coefficient matrix; returns the identity.
  - `noncomputable def rref ... := sorry` — an explicit placeholder;
    still forbidden, same reasons.

  What to do if you can't implement it: narrow the Phase 1 issue,
  commit only the declarations you *can* correctly implement,
  document (in the PR description) which SPEC declarations are being
  deferred to a follow-up issue, and open that follow-up. Don't
  commit stubs to keep the PR "complete" — an incomplete but honest
  Phase 1 is strictly better than a complete-looking one with
  placeholders.

- **`sorry`'d theorem proofs are expected.** The point of scaffolding
  is to get the API surface compiling, not to fill in proofs. This
  rule applies to `theorem` bodies and propositional `structure`
  fields — those produce `Prop` values, and a `sorry` proof doesn't
  propagate into computation. It does **not** extend an escape
  valve for data-level bodies — see the rule above.

- **Helper definitions** not in the SPEC are fine if needed to state
  the API. Note them in the PR. The same "correctly implemented or
  not committed" rule applies.

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

- every SPEC declaration that has been implemented in Lean has a
  signature matching the SPEC, and a body that correctly implements
  the SPEC contract (no `sorry`, no `axiom`, no wrong-but-plausible
  trivial body);
- SPEC declarations that have *not* yet been correctly implemented
  are not present in Lean — the PR description records which ones
  are deferred to follow-ups, and a follow-up issue exists for each;
- `lake build <HexFooLib>` succeeds;
- each new `.lean` file carries a module docstring summarising the
  library contents;
- no `TODO`, `FIXME`, or `...` placeholder remains in the scaffolded
  code (other than `sorry` in proofs).

Record completion by bumping `libraries.yml[L].done_through` to `1`.
