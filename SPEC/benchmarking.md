# Benchmarking

This document specifies the performance-measurement contract for the
project. It complements [testing.md](testing.md): testing asks whether
the implementation is correct, benchmarking asks how fast the verified
implementation is and how it compares with reference systems.

Benchmarking is part of the SPEC, not an afterthought. The project is
building executable computational algebra, so every major library must
have named benchmark cases, reproducible harnesses, and published
results.

## Goals

Benchmarking serves four purposes:

1. Detect performance regressions in Lean implementations over time.
2. Compare alternative verified algorithms or representations.
3. Compare Lean implementations against external CAS/reference tools.
4. Provide concrete evidence for design decisions in the library specs.

Benchmarks do **not** relax the requirement that all trusted runtime
computation happens in Lean. External tools are used as comparators and
oracles for measurement only.

## Benchmark classes

Each computational library must define both microbenchmarks and
end-to-end benchmarks.

### Required microbenchmarks

- `hex-poly-fp`: addition, multiplication, modular reduction, GCD,
  exponentiation mod `f`, Rabin/Berlekamp irreducibility kernels
- `hex-poly-z`: multiplication, division/remainder, content/primitive
  part, GCD
- `hex-berlekamp`: Berlekamp matrix construction, nullspace, factor
  splitting, irreducibility tests
- `hex-hensel`: linear lifting and quadratic lifting on the same named
  inputs
- `hex-lll`: size reduction, swap-heavy inputs, full reduction
- `hex-gfq-ring` / `hex-gfq-field` / `hex-gfq`: multiplication,
  inversion, Frobenius, norm/trace on representative `(p, n)` pairs
- `hex-conway`: Tier 1 irreducibility verification, Tier 2 Conway-table
  verification, and Tier 3 search when implemented

### Required end-to-end benchmarks

- finite-field construction for named `(p, n)` pairs
- irreducibility certification for named polynomials over `F_p`
- integer polynomial factorization on small and medium examples
- end-to-end Berlekamp-Zassenhaus with and without LLL when both paths
  exist

## Required comparisons

The benchmark suite must include direct comparisons where they are
architecturally important.

- `GF2Poly` vs `FpPoly 2`
- Barrett vs Montgomery crossover regimes
- linear vs quadratic Hensel lifting
- exponential recombination vs LLL-assisted recombination
- Tier 1 vs Tier 2 Conway verification costs
- Tier 2 Conway verification vs Tier 3 Conway search

## External comparison tools

The benchmark harness should compare against the strongest practical
reference available for each task.

- GAP: Conway polynomial tables, Conway compatibility checks, primitive
  polynomial checks
- PARI/GP: finite-field irreducibility checks and large-degree
  irreducibility experiments
- FLINT: dense polynomial arithmetic and integer polynomial factoring
- SageMath: higher-level reference workflows where it offers a simpler
  orchestration layer than direct FLINT/PARI calls
- fpLLL: lattice reduction comparisons

The spec does not require every machine to have every external tool
preinstalled. The harness may provision tools via Nix, containers, or
documented local setup, but the provisioning path must itself be
reproducible.

## Reproducibility contract

Every benchmark run must be reproducible from committed inputs and
metadata.

- Each benchmark case has a stable name.
- Randomized benchmarks use fixed committed seeds.
- Generated inputs that matter for comparisons are either committed or
  regenerated deterministically from the seed and recorded parameters.
- Output artifacts record the Git commit, benchmark harness version,
  machine description, date, Lean toolchain, and external tool versions.
- Failures and timeouts are recorded explicitly rather than silently
  dropped.

## Conway benchmarks

The `hex-conway` benchmark suite must reflect the three-tier design.

### Tier 1

Measure verification of irreducibility for committed imported Conway
polynomials. These runs answer: how expensive is it to certify a known
modulus for `GF(p^n)`?

### Tier 2

Measure full verification of committed imported Conway entries:

- irreducible
- primitive
- compatibility with divisor-degree entries

These runs answer: how expensive is it to certify the imported table as
Conway data?

### Tier 3

Measure explicit search for missing Conway polynomials when implemented.
Tier 3 benchmarks must be reported separately from Tier 1 and Tier 2.
The benchmark report must never aggregate them into a single
"hex-conway runtime" number.

Named `hex-conway` cases should include:

- existing table entries near the top of the Lübeck table for small
  primes, such as `(2, 409)`, `(3, 263)`, `(5, 251)`
- existing table entries for medium and large primes, such as
  `(97, 127)`, `(521, 13)`, `(65537, 7)`
- just-beyond-table search probes, such as `(2, 410)`, `(97, 128)`,
  `(521, 17)`, `(65537, 8)`, or updated analogues if the committed table
  changes
- large-degree irreducibility stress tests over `F_2`, e.g. degrees
  `512`, `1024`, `2048`, `4096`, `8192`, and beyond when feasible

## Output artifacts

Benchmark runs must produce machine-readable and human-readable outputs.

- machine-readable summary, e.g. JSON or CSV
- raw logs for replay/debugging
- rendered HTML report pages for human inspection

The HTML reports are required project artifacts.

## Publication contract

Benchmark outputs must be published to GitHub Pages associated with the
repository.

- the repo contains a workflow or documented script that renders HTML
  benchmark reports
- rendered reports are published on GitHub Pages
- the repo `README.md` links to the benchmark index page
- the benchmark index page links to individual runs or release snapshots
- release or milestone notes should link to the corresponding benchmark
  pages

The goal is that a reader can move from the repository front page to the
current benchmark dashboard with one click.

## CI and release expectations

Not every benchmark must run on every PR, but the contract must say
which ones run where.

- smoke benchmarks may run on PRs
- the full benchmark suite may run on a scheduled workflow or
  release-candidate workflow
- each release target must name the benchmark cases it must pass
- a release is blocked by obvious performance regressions even if proofs
  are complete

## Relationship to conformance testing

Conformance and benchmarking should share harness infrastructure when
useful, but they remain distinct:

- conformance asks whether Lean and the reference agree
- benchmarking asks how long Lean and the reference take

The same named cases should usually support both views.
