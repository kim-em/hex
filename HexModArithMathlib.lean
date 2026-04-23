import HexModArithMathlib.ZMod64
import HexModArithMathlib.Conformance

/-!
Mathlib bridge scaffolding for `HexModArith`.

This root module re-exports the initial `HexModArithMathlib` bridge
surface: the concrete conversions between `HexModArith.ZMod64 p` and
Mathlib's `ZMod p`, the scaffolded ring equivalence, and the basic
representative/cast transport lemmas that downstream bridge libraries
will use. The Phase 3 `Conformance` module adds deterministic checks
for the conversion pair, round-trip identities, representative
preservation, and cast transport on committed small moduli.
-/

namespace HexModArithMathlib
