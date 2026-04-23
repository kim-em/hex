import HexPoly.DensePoly
import HexPoly.Arithmetic
import HexPoly.Division
import HexPoly.Gcd
import HexPoly.Crt
import HexPoly.Eval
import HexPoly.Content
import HexPoly.Conformance
import HexPoly.Benchmark

/-!
Core dense polynomial declarations.

This root module re-exports the dense representation and arithmetic
scaffolds used by downstream polynomial libraries, including the
quotient/remainder division, GCD, CRT, evaluation, composition, and
derivative surfaces together with the integer content and primitive-part
layer plus the committed `core` conformance checks for the executable
evaluation, arithmetic, division, and GCD APIs, and the first stable
Phase 4 benchmark-fixture registry for multiplication, monic division,
and GCD/XGCD workloads.
-/

namespace HexPoly
