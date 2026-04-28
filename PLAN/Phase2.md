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
- **Does every committed `def` / data-carrying `structure` field /
  `class` / `instance` body actually implement the SPEC contract
  correctly?** [PLAN/Phase1.md](Phase1.md) forbids data-level
  placeholders of any kind — no `sorry` bodies, no `axiom`s
  standing in for data, no trivial returns (input unchanged, `0`,
  `Matrix.identity`, `none`, empty list). A library must commit
  only the declarations it can correctly implement; everything
  else stays out of Lean until a later PR implements it. Flag any
  committed declaration whose body is a placeholder in any of
  these forms. Flagged bodies must be deleted (and any downstream
  callers updated) in a follow-up issue before the
  `scaffolding-reviewed` token is committed — either the
  implementation becomes correct, or the declaration leaves the
  tree. "Rewrite as `sorry`" is **not** an acceptable fix.
- **Does each data-level body match the SPEC's intended algorithmic
  shape — not just its input/output contract?** Flag any body that
  produces the right output via an unrelated algorithm: a full
  rebuild where the SPEC prescribes an in-place update; a
  reference implementation behind a name that promises the
  optimised version; a detour through canonical form when the SPEC
  gives explicit update formulas. These are "wrong-shape" scaffolds
  and are forbidden by [PLAN/Phase1.md](Phase1.md), same remedy as
  wrong-output scaffolds: fix the body, or delete the declaration.
- **For each `@[extern]` in the library, open its C body in
  `HexFoo/ffi/<name>.c` and confirm it does work native to C.** A C
  body that consists of (or reduces to) `return l_Hex_*___boxed(a,
  b);` — i.e. a trampoline back to the Lean runtime — is a fake
  extern. Remedy: delete the `@[extern]` attribute, delete the C
  file, drop the `moreLinkArgs`/`moreLeancArgs` entry in the
  lakefile, and open a follow-up issue for the real extern.
- **For each declaration whose name or signature mentions a native
  numeric type (`UInt64`, `UInt32`, `UInt8`, `Float`, `Fin n`,
  ...), confirm the body uses native arithmetic on that type.** A
  body that converts to `Nat`/`Int`, runs the Nat-level algorithm,
  and converts back is a wrong-shape scaffold even when the
  input/output contract is satisfied: the asymptotic complexity is
  bignum, not the native single-word cost the type promises.
- **Grep the library for the words `scaffold`, `for now`,
  `eventual`, `placeholder`, `Phase 1`, `bridge for` in `*.lean`
  and `ffi/*.c` files.** Every hit is a candidate violation; flag
  in the review issue.
- **Does each data-level `def` body match the algorithm named in the
  library SPEC for its operation?** [PLAN/Phase1.md](Phase1.md)
  forbids "alternative implementations with the wrong algorithmic
  complexity"; this question makes the rule enforceable at review
  time. Per [SPEC/design-principles.md §7](../SPEC/design-principles.md),
  the binding complexity contract for an operation lives in its
  library's SPEC: `hex-arith.md` names the algorithm for `powMod` and
  `extGcd`, `hex-poly-z.md` for `binom` / `floorSqrt`, and so on.
  Read the SPEC bullet for each declaration before judging its body,
  and flag any body whose algorithmic shape doesn't match the
  library SPEC's named algorithm — linear-time `pow` where
  square-and-multiply was named, `a^n % p` where Nat-level
  square-and-multiply was named, descending linear-scan `floorSqrt`
  where Newton was named, unmemoised Pascal `binom` where the
  multiplicative formula was named, rebuild-from-scratch where an
  in-place update was named. If a library SPEC bullet names only
  "exponentiation" / "binomial coefficient" without naming an
  algorithm, that's a SPEC gap — file a SPEC issue alongside any
  implementation issue. Same remedy as wrong-shape scaffolds: fix
  the body to match the SPEC, fix the SPEC to name the canonical
  algorithm, or delete the declaration.
- **Are there one-line aliases of an adjacent declaration, lemmas
  duplicating Lean core, or names that misrepresent the body?**
  Flag any `def`/`theorem` whose body is `exact <other-decl>` for
  an `<other-decl>` defined in the same file (it should be deleted
  and call sites pointed at the real declaration). Flag any local
  `Nat`/`Int`/`UInt64`/`Array`/`List` lemma whose statement
  matches a same-shape declaration in `Init.*` or the Lean stdlib
  (it should be deleted and call sites pointed at the core lemma).
  Flag any name whose verb or qualifier doesn't appear anywhere in
  the body (e.g. a lemma named `foo_sub_bar` whose statement
  contains no subtraction).

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
