# Conformance testing

Conformance testing is a tiered system rather than one monolithic
workflow. The repository should support at least three profiles:

- `core` — deterministic Lean-side checks with no external dependencies
- `ci` — modest randomized cross-checks, using external tools only when
  available
- `local` — developer-driven runs with customizable sizes and tools

Every failure must be replayable by recording the library name, test
profile, seed, and fully serialized input case.

## Oracle strategy

External tools are used for **testing**, not for algorithms — all actual
computation still runs in Lean. But the project should not route every
test through the same oracle stack. The intended oracle choices are:

- `hex-arith` — Lean's built-in `Nat` / `Int` big integer semantics
- `hex-mod-arith` — Lean big-integer modular arithmetic
- `hex-poly`, `hex-poly-z`, `hex-poly-fp` — FLINT or Sage polynomial
  arithmetic
- `hex-matrix`, `hex-gram-schmidt` — Sage exact matrix / rational linear
  algebra
- `hex-gf2`, `hex-gfq-ring`, `hex-gfq-field`, `hex-gfq` — Sage finite
  field and quotient-ring computations
- `hex-berlekamp`, `hex-berlekamp-zassenhaus` — FLINT or Sage
  factorization / irreducibility checks
- `hex-hensel` — Sage or FLINT Hensel-lifting support, plus direct
  congruence/product checks
- `hex-lll` — fpLLL, or Sage's `LLL`, comparing reducedness, lattice
  equality, and determinant preservation rather than exact basis equality
- `hex-conway` — committed database fixtures cross-checked against Sage's
  Conway tables, not random generation

The `-mathlib` bridge libraries are not the primary target of external
conformance testing. They should rely mainly on internal equivalence /
property tests plus the conformance coverage of the computational
libraries.

Python-accessible wrappers may reduce dependence on full Sage for some
layers. In particular, `python-flint` is a suitable oracle candidate for
much of the `hex-poly` / `hex-poly-z` / `hex-poly-fp` surface. But Sage
remains the preferred umbrella oracle for the mixed finite-field,
quotient-ring, exact linear algebra, Conway, and cross-library
factorization workflows.

## Profile sizes

The spec should define size policies per profile. The exact values may
live in named constants rather than being hard-coded in prose, but every
generator must be parameterized by size bounds and seed.

- `core`: tiny deterministic cases only
  Examples: polynomial degrees up to about `8-12`, matrix dimensions up
  to about `6-8`, finite-field extensions up to degree `6`, LLL
  dimensions up to about `10`.
- `ci`: modest randomized cases
  Examples: integer/finite-field polynomial degrees around `16-32`,
  coefficient bit-sizes around `8-32`, Hensel lift exponents around
  `2-5`, and LLL dimensions around `15-25` with small entries.
- `local`: larger campaigns
  More seeds, larger degrees/dimensions, optional high-cost oracles, and
  manually triggered runs that would be too expensive for standard CI.

CI defaults must remain small enough to tolerate partial external-tool
availability and ordinary GitHub-hosted runners.

## Infrastructure contract

Lean should produce and consume a simple serialized case/result format,
preferably JSON or JSONL, for:

- polynomials
- matrices
- lattice bases
- primes / modulus choices
- expected normalized outputs

Python or shell driver scripts are responsible for:

- detecting which tools are installed
- invoking external oracles
- normalizing oracle outputs into the shared format
- gracefully skipping checks when an optional tool is unavailable

The spec should define at least three execution modes:

- `always` — no external tools; must run everywhere
- `if_available` — run oracle-backed conformance checks only for tools
  present on the machine
- `required` — manual jobs that fail if declared tools are
  missing

## Sage strategy

Sage is important enough to deserve an explicit deployment story.
Ubuntu's `apt` packages are not a stable basis for Sage-backed CI, so
the preferred path should be a Nix-based Sage job:

- local use via `nix shell nixpkgs#sage --command ...`
- CI use via `cachix/install-nix-action` followed by Sage commands
  through `nix shell`

This keeps local and CI execution closer together and avoids depending
on Ubuntu package availability. A conda-forge Sage install is an
acceptable secondary path for local experimentation, but the spec should
not require it as the primary CI mechanism.

This file specifies correctness-oriented cross-checking only. Performance
measurement, benchmark case definitions, external timing comparisons,
and publication of benchmark reports on GitHub Pages are specified in
[benchmarking.md](benchmarking.md).
