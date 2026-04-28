**Accomplished**

Rewrote the Phase-4 (benchmarking) doctrine around `kim-em/lean-bench`
and promoted "scaffolding is for proofs only" to a project-wide
principle. Single commit on `spec/benchmarking-rewrite-lean-bench`:

- [SPEC/benchmarking.md](../SPEC/benchmarking.md) — substantial
  rewrite. New structure: why benchmark, the verdict-as-bug-trigger
  model with the HexArith Montgomery / HexLLL swapStep findings as
  worked examples, lean-bench as the only harness (with the lakefile
  snippet and both `setup_benchmark` / `setup_fixed_benchmark`
  forms), within-Lean comparisons via `compare`, external
  comparators via FFI (preferred) or process call, fixed-problem
  benchmarks, Conway tier separation, CI integration via
  `lake exe ... verify`, reproducibility contract, and an explicit
  anti-patterns list distilled from the prototype.
- [SPEC/design-principles.md](../SPEC/design-principles.md) — added
  principle 7: scaffolding applies only to proofs. Every `def` ships
  with the intended-final implementation; the rule is enforced at
  Phase 1 (author), Phase 2 (review), and Phase 4 (benchmark
  verdict).
- [SPEC/testing.md](../SPEC/testing.md) — preamble now cross-links
  the bug-finding doctrine; conformance and benchmarking share one
  loop. Scaffold-locking `#guard`s text references the new
  principle 7.
- [PLAN/Conventions.md](../PLAN/Conventions.md) — three additions:
  "Scaffolding is for proofs only" under Hard rules; "Rollback is
  a normal action" under `done_through` semantics (operational
  steps for a backward bump); "Bench-found and conformance-found
  issues" issue template under Issue creation.
- [PLAN/Phase4.md](../PLAN/Phase4.md) — replaced. Phase 4
  deliverable is `HexFoo/Bench.lean` with `setup_benchmark`
  registrations using *textbook* complexity. An `inconclusive`
  verdict is not a Phase 4 exit; it triggers a rollback.

Filed [kim-em/lean-bench#24](https://github.com/kim-em/lean-bench/issues/24)
during planning ("Fixed-problem benchmarks (no parameter sweep)"),
implemented in
[kim-em/lean-bench#26](https://github.com/kim-em/lean-bench/pull/26).
The SPEC references both `setup_benchmark` and `setup_fixed_benchmark`
because both now exist.

Imported the prototype retrospective at
[progress/2026-04-23T12:57:18Z_bench-prototype.md](2026-04-23T12:57:18Z_bench-prototype.md)
into git so the reasoning behind the rewrite is preserved. Removed
TODO.md (its content is now in the SPEC).

**Current frontier**

The SPEC rewrite is committed but not pushed. The Phase-4 prototype
implementation (HexArith/Bench/, HexLLL/Bench/, scripts/bench/,
working-tree edits to lakefile.toml and HexArith.lean / HexLLL.lean
and .github/workflows/ci.yml) is still in the working tree —
deliberately untouched per Kim's direction; a separate rollback PR
will handle it.

**Next step**

- Push branch and open the SPEC rewrite PR.
- Kim handles the broader rollback (Phase-4 prototype + any older
  committed Phase-4 fixture work like HexArith/Benchmark.lean and
  HexManual/Benchmarks/index.md) in a follow-up.
- After the rewrite lands, when a library re-enters Phase 4, that PR
  adds `[[require]] name = "lean-bench"` to the lakefile and creates
  the first `HexFoo/Bench.lean`.

**Blockers**

None.
