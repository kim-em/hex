import HexHenselMathlib.Basic

/-!
The `HexHenselMathlib` library transfers the executable `HexHensel` surface to
Mathlib's `Polynomial ℤ` API.

Its initial Phase 1 surface focuses on the coprimality-lifting infrastructure
used by later Hensel-correctness and uniqueness arguments: reduction-map
compatibility across `ZMod (p^k)`, coefficientwise divisibility transport, and
the `coprime_mod_p_lifts` theorem statement.
-/
