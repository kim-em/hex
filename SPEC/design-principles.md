# Design principles

1. **Many small libraries** in a single monorepo, each its own Lake
   library target.

2. **No Mathlib in the computational core.** Every library that computes
   something is Mathlib-free. Where full correctness requires results
   from analysis (e.g. the Mignotte bound), the computational
   library proves conditional correctness and the corresponding
   `-mathlib` library discharges the hypothesis. The `-mathlib`
   libraries also prove correspondence with Mathlib's mathematical
   definitions (e.g. `ZMod64 p ≃+* ZMod p`).

3. **Performant by default.** Dense array-backed representations, `UInt64`
   coefficients for `F_p`, Barrett/Montgomery reduction for modular
   arithmetic. New GMP `@[extern]` primitives where Lean's runtime
   doesn't yet expose what we need (notably extended GCD for big
   integers). FLINT is used for conformance testing, not as a runtime
   dependency.

4. **Lean algorithms from the start.** All algorithms are implemented and
   run in Lean natively. No external CAS in the loop. Certificate
   structures exist for compact proof witnesses, but the algorithms that
   generate and check certificates are both in Lean.

5. **Clear DAG structure.** Libraries can be developed in parallel. LLL has
   no dependency on polynomial arithmetic. Hensel lifting is independent of
   LLL. Everything meets at the top (Berlekamp-Zassenhaus).

6. **`Hex` namespace.** All definitions live under `Hex` to avoid
   collisions with Mathlib's root-namespace types (`Matrix`,
   `Polynomial`, etc.).

7. **Scaffolding applies only to proofs.** A proof skeleton may carry
   `sorry` placeholders, where allowed. Every `def`, data-carrying
   `structure` field, `class`, and `instance` ships with its
   intended-final implementation on the first commit — the *real*
   algorithm with the *intended* complexity, not a wrong-but-plausible
   stand-in. If you cannot write that implementation in the current
   session, do not commit the declaration; leave it out of Lean
   entirely and open a follow-up issue. This rule is enforced at
   three points: when a library is scaffolded
   ([PLAN/Phase1.md](../PLAN/Phase1.md)), when its scaffolding is
   reviewed ([PLAN/Phase2.md](../PLAN/Phase2.md)), and when its
   benchmarks run ([benchmarking.md](benchmarking.md)). If
   benchmarking later reveals that a committed `def` was scaffolding
   in disguise — wrong shape, wrong complexity — the response is to
   roll back the affected library's `done_through` and re-enter the
   relevant phase, not to weaken the benchmark.

   **Canonical fast defaults for standard operations.** A SPEC that
   says only "exponentiation", "binomial coefficient", or
   "square root" without naming an algorithm does NOT license the
   textbook-recursive body. Scaffolders default to the canonical fast
   algorithm for the operation, even when the SPEC is silent. The
   table below lists the defaults that have already cost reviewer
   time on this project; it is not exhaustive but is binding for the
   listed operations.

   | Operation                                                              | Canonical fast default                         | Forbidden naive shape                                                |
   | ---------------------------------------------------------------------- | ---------------------------------------------- | -------------------------------------------------------------------- |
   | `pow x n` in any monoid / group / ring / field                         | square-and-multiply, `O(log n)` ops            | `pow x (n+1) = mul (pow x n) x` (or any linear-time accumulator)     |
   | Modular exponentiation `a^n mod p` at `Nat`                            | square-and-multiply, reducing after each mul   | `a^n % p` (full-precision exponent before reducing)                  |
   | Frobenius `frob(a) = a^p` in `F_p[x]/(f)`                              | square-and-multiply via `pow`                  | `Nat.rec` over `p` (cryptographic `p` is `~2^31`+)                   |
   | `gcd` / `extGcd` in any Euclidean domain                               | Euclidean algorithm, tail-recursive            | linear search; recursive Bezout build-up that's not tail-recursive   |
   | Integer floor square root                                              | Newton iteration, `O(log n)`                   | descending linear scan from `n` down to `√n`                         |
   | Binomial coefficient `C(n, k)`                                         | multiplicative formula `(∏ i<k, (n−i)) / k!`   | unmemoised Pascal recursion (`Θ(2^k)` calls)                         |
   | Modular reduction inside a hot loop (Frobenius, polynomial eval)       | Barrett (`p < 2^32`) / Montgomery (general)    | naive `%` in the inner loop                                          |
   | Native-word arithmetic on `UInt64` / `UInt32` / `Fin n`                | the typed operation directly                   | `toNat → Nat → .ofNat` round-trip (boxes the bignum cost in)         |
   | `nsmul n x` / `natCast n` in a ring with fast `pow`                    | binary decomposition (or share `pow`'s code)   | linear `Nat.rec` over `n`                                            |
   | In-place update (Bareiss step, GS row update, LLL swap)                | mutate or thread state through the recurrence  | rebuild the matrix/basis from scratch each iteration                 |
   | Linear search across a structure with a known fast lookup              | the fast lookup                                | walk the whole structure regardless                                  |

   The list is consulted by the Phase 2 review checklist when judging
   whether a body is "wrong-complexity" in the absence of an explicit
   SPEC contract: an entry on the list is treated as if the SPEC said
   "use the canonical fast default" for that row's operation. If a
   library's SPEC genuinely wants the slow variant (e.g. for a proof
   reference that's never called at runtime), it must say so
   explicitly — and the corresponding `def` must be private and
   un-imported by hot-path code. Entries on the list aren't a complete
   formal definition; scaffolders confronting an operation not on the
   list pick what a textbook calls "the standard fast algorithm" for
   that operation, and open a clarification issue if the choice
   requires a SPEC tradeoff (e.g. Karatsuba threshold, Barrett vs.
   Montgomery selection).

## Fully autonomous execution

The project runs without human interaction after launch. Lean, Mathlib,
and this SPEC are fixed inputs. Agents resolve every issue they
encounter:

- If a needed result is not in Mathlib, prove it locally.
- If a tactic misbehaves, work around it.

There is no human escalation channel. "Stop and flag" is not an
option; "decide and proceed" is.

### Scope of autonomous SPEC edits

Agents may edit the SPEC only to fix clauses that are ill-typed,
internally contradictory, or clearly mathematically impossible. Every
such edit is accompanied by an explicit rationale in the PR
description citing the offending clause and the project goal that
breaks the tie. Changes to public APIs or release goals are
exceptional and should be called out as such, even though no human
approves them. Routine refactoring and "I would have written it
differently" are not grounds for SPEC edits.

### Push sorries earlier

When a proof is hard, replace it with a proof outline that cites new, clearly-stated lemmas
(which may themselves be `sorry`) one level closer to the
foundations. Repeat until the remaining sorries are individually
plausible. This keeps the proof graph reviewable even when the
leaves are incomplete, and lets later workers attack foundational
lemmas in isolation.

## Naming and documentation

**Namespaces.** New types, functions, and theorems introduced by this
project live under `Hex` (e.g. `Hex.FpPoly`, `Hex.GF2n`). Additions to
existing Lean/Mathlib datatypes live in the original namespace
(`Nat.foo`, `Array.polyProduct`, `UInt64.mulHi`). Subnamespaces like
`Hex.GramSchmidt.Int` are fine when they aid discoverability.

**Docstrings.** All public `def`/`structure`/`class`/`inductive`
declarations carry a docstring. Non-obvious private helpers — anything
encoding an invariant, a subtle algorithmic choice, or a non-trivial
specification — also carry one. Routine private plumbing (unfolding
lemmas, `_aux` helpers, trivial getters) is exempt. Every theorem
another file could reasonably import carries a docstring stating what
it proves and why the caller cares.
