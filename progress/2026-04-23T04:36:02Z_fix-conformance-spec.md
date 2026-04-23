**Accomplished**

- Rewrote `SPEC/testing.md` to specify a prescriptive per-library
  `Conformance.lean` module contract: required docstring declaring
  oracle / mode / covered operations / properties / edge cases;
  minimum three cases per operation (typical / edge / adversarial);
  explicit banned anti-patterns naming the ceremony we just saw
  (dead `expectedX` fields, serialise-roundtrip-to-literal,
  metadata `def`s with no consumer, single-case fixtures, literal
  duplication, trivial `by decide`, `native_decide`); preferred
  idioms `#guard_msgs in #eval` for spot values and `#guard` for
  properties; mandate that `core` runs on every push/PR.
- Tightened `PLAN/Phase3.md` exit criteria to match, including a
  reviewer checklist agents and reviewers can run against PRs.
- Deleted the three existing low-quality `Conformance.lean` modules
  (`HexArith/`, `HexPoly/`, `HexMatrix/`) and their root-module
  imports.
- Wrote a new reference `HexArith/Conformance.lean` following the
  new contract: module docstring naming oracle/mode/coverage, then
  `#guard_msgs in #eval` for spot values and `#guard` for Bézout /
  `Nat.gcd` / `a ^ n % p` / Barrett / Montgomery round-trip and
  identity properties, with ≥3 cases per operation. Sidesteps the
  interpreter-missing-extern issue for `HexArith.Int.extGcd` by
  exercising `Hex.pureIntExtGcd` and asserting extern agreement
  by `rfl`.
- Replaced the `conformance.yml` stub with a real workflow that
  runs on push-to-main and pull_request, building each committed
  `HexFoo/Conformance.lean` individually so failures are visibly
  attributable to the library whose checks regressed.
- Verified with `lake build` (3481 jobs, all green; new HexArith
  conformance module elaborates with all `#guard`s passing).

**Current frontier**

- The conformance spec rewrite, the reference `HexArith` module,
  and the CI wiring are ready to land together as one PR. Issues
  `#138`, `#140`, `#142`, `#150` cover the now-deleted or
  incompatible conformance work and should be closed with pointers
  to the new SPEC so any future redispatch follows the new rules.

**Next step**

- Open the PR (`fix-conformance-spec`) with auto-merge, then close
  the four stale issues referencing `SPEC/testing.md`. Planner can
  redispatch Phase 3 for `HexPoly` and `HexMatrix` against the new
  reference once merged.

**Blockers**

- None.
