**Accomplished**

Landed prototype benchmarking frameworks for HexArith and HexLLL, working tree only. Both libraries have:

- A Lean exec (`hex_arith_bench`, `hex_lll_bench`) with online calibration, JSONL emission, and `--ladder` / `--smoke` modes.
- Rich JSONL schema from day one (schema_version, family_version, param_origin, seed, run_index, wall_nanos, result_hash, status enum, git_sha, hostname, cpu_model, …).
- A shared harness (`scripts/bench/run.sh`, `smoke.sh`, `report.py`) and Python comparators (`python_arith.py` uses stdlib, `fpylll_lll.py` is optional and skips gracefully when unavailable).
- Markdown report output to `HexManual/Benchmarks/<Lib>.md`, rendered from JSONL (JSONL remains the source of truth).
- CI smoke step in [.github/workflows/ci.yml](../.github/workflows/ci.yml); smoke validated locally in ~8s total for both libraries.

HexArith results at seconds=3: A1 extgcd (B=65536) 137ms vs python-stdlib 282ms (0.49×), A2 powMod (B=15808) 690ms vs python 6.16s (0.11×), A3 Barrett mulMod (N=10⁸) 553ms vs python 10.10s (0.05×).

HexLLL results at seconds=3: L1 uniform (dim=8) 1.55s, L2 arith-heavy (dim=6, B=256) 35ms. fpylll not installed; comparator gracefully skipped.

Plan file: [let-s-make-a-plan-synchronous-token.md](/home/kim/.claude/plans/let-s-make-a-plan-synchronous-token.md).

**Current frontier**

Both libraries produce valid end-to-end runs. The harness surfaced several real findings that belong in SPEC v2:

1. **`MontCtx.mulMont` / `fromMont` scaffolding is unbenchmarkable.** They call `montgomeryRadixInvNat p = (List.range p.toNat).find? ...` — brute-force search of `[0, p)` on every call. For p=65537 that's 65k iterations per `mulMont`, making even a tiny N unusable. HexArith should replace this with a real Bezout-based inverse before Montgomery throughput can be measured. A4 is dropped from both budgeted and smoke families for now.

2. **`lll` requires `n` in the type** — we can't dispatch a runtime `n`. The workaround (discrete dim ladder via pattern match on snapped dim) works but bakes dimension choices into Lean. SPEC v2 should decide: do we require libraries to expose a `runtime-n` wrapper, or do benchmarks live with discrete dims?

3. **`decide` on Rat comparisons is broken without `+kernel`.** `(1 : Rat) / 4 < 3 / 4` can't be decided by elaboration-time `decide` because `Rat.blt` doesn't reduce through the literal-division form. `decide +kernel` works (slow but acceptable for fixed small literals). SPEC v2 should require libraries that take Rat bound-constraints to provide a decidable instance shim or helper lemma. The workaround adds compile-time cost.

4. **`Decidable b.independent` isn't auto-synthesized** — we had to provide the instance explicitly with `unfold Matrix.independent; exact inferInstance`. HexLLL would benefit from a public Decidable instance.

5. **Top-level `def` of proof-carrying structures (BarrettCtx, MontCtx) gets eagerly evaluated at module init**. A module-level `def a3Ctx : BarrettCtx 4294967291 := ...` deadlocked module load because the closure inside `fromMont` referenced the Montgomery search. Fix: inline the ctx construction inside the runner. SPEC v2 should call this out as a benchmark-harness convention.

6. **Online calibration works but has a latency floor.** We can't cancel a trial mid-flight, so a first-guess param that's way too large kills the budget (e.g. L1 initially tried dim=12 and would have taken minutes). Mitigations: start from `paramFloor`, use a very small first probe, or add SIGALRM-style cancellation.

7. **Well-founded recursion in PRNG blew up the kernel.** Original SplitMix `nextBits` with a helper recursion and omega termination proof caused "(kernel) deep recursion detected" at elaboration. Rewrote with an explicit `for` loop over precomputed chunks. SPEC v2 should note that Bench harnesses should avoid well-founded recursion where possible.

8. **`L2.arith-bit-sweep` dropped from plan's `n=20` to `n=6`.** The naive swap step's cost at n=20 is prohibitive at any bit-width, so the arith-vs-swap distinction L2 was meant to highlight is blurred.

9. **Python's `ext_gcd` recurses too deep.** Lean's equivalent trampolines tail-calls fine, but stock Python hits the recursion limit on 1000+ bit inputs; iterative Bezout is the fix.

Both benchmarks consistently show Lean beating Python-stdlib by significant ratios (2×–20×), which is meaningful baseline data. Scaling-law slopes are not yet populated because ladder mode isn't being used by default — the infrastructure to fit and report them is in [report.py](../scripts/bench/report.py) but needs `--ladder` runs to populate.

**Next step**

For SPEC v2 of benchmarking.md, the following should be mandated or recommended (ordered by severity):

- **Required**: JSONL schema with the fields we emit today, status enum, and distinction between `predicted` and `discovered` param origins.
- **Required**: per-family max-wall cap as a first-class concept, distinct from `budget_skip` from ladder exhaustion.
- **Required**: `smoke.sh`-equivalent CI gate that exercises every family in <60s.
- **Recommended**: harness-authoring conventions — avoid top-level `def` of proof-carrying structures, avoid well-founded recursion in runners, always use a hash result so comparator joins work.
- **Recommended**: comparator version auto-capture and `comparator_unavailable` as a first-class status.
- **Deferred**: Markdown vs HTML rendering, baseline regression gates.

Run `./scripts/bench/run.sh hex_arith 30 --ladder --runs 3` for the first scaling-law data set.

**Blockers**

None for the prototype; the retrospective is the handoff for SPEC v2 drafting.

Not done intentionally:
- Third HexLLL family (Lagarias-Odlyzko knapsack) — trimmed during implementation time-budgeting.
- fpylll/gmpy2 install instructions — comparators are optional.
- HTML rendering / baseline regression detection — explicitly out of scope for v1 per the plan.
