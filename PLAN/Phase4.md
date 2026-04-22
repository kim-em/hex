# Phase 4: Performance and Benchmarking

**Coupling:** dep-coupled. Library L can start Phase 4 once
`libraries.yml[L].done_through ≥ 3` and every `d ∈ L.deps` has
`libraries.yml[d].done_through ≥ 4`.

Performance is part of the project spec, not an optional cleanup task.
Before calling a release target successful, measure the cost of the
native Lean implementations on representative workloads.

## Goals

- Catch major performance regressions early.
- Validate that specialized code paths (`UInt64`, Barrett/Montgomery,
  packed GF(2), d-representation LLL) are actually paying for their
  complexity.
- Keep the finite-field-oriented releases honest: field construction and
  irreducibility checking must be usable, not merely correct on paper.

## Scope

- **hex-mod-arith:** modular multiply, inverse, exponentiation.
- **hex-poly / hex-poly-fp:** multiply, div/mod, GCD, Frobenius powers.
- **hex-gf2:** packed multiply, modular reduction, GCD, `GF(2^n)` ops.
- **hex-berlekamp:** Berlekamp matrix construction, nullspace, factor
  splits, Rabin test.
- **hex-hensel:** linear lifting baseline; quadratic lifting once added.
- **hex-lll:** size reduction, swap-heavy cases, full reduction.
- **hex-gfq / hex-gfq-field:** field multiplication/inversion for
  representative `(p, n)` pairs.
- **hex-berlekamp-zassenhaus:** end-to-end factoring on small and
  medium examples, with and without LLL where both paths exist.

## Benchmark discipline

- Maintain a small committed benchmark suite with fixed seeds and named
  inputs so regressions are reproducible.
- Benchmark both micro-kernels and end-to-end workflows.
- Track at least relative comparisons where they matter:
  - `GF2Poly` vs `FpPoly 2`
  - Barrett vs Montgomery crossover regimes
  - linear vs quadratic Hensel lifting
  - exponential recombination vs LLL-assisted recombination
- Keep benchmarking separate from proof obligations: benchmark the
  executable code path actually used at runtime.

## Release expectations

- Each release target must name the benchmark cases it must pass.
- Specific cases and thresholds may evolve between releases, but every
  such change must be accompanied by a short rationale in the PR that
  changes the benchmark set (one paragraph per change). This keeps the
  release gate machine-checkable without freezing the case list, and
  keeps release-specific churn out of `SPEC/`.
- A release is blocked by obvious performance pathologies even if proofs
  are complete.
- Record benchmark results in PRs or milestone notes so the orchestrator
  can detect regressions over time.

Record completion by bumping `libraries.yml[L].done_through` to `4`.
