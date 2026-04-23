import HexGramSchmidt.Int
import HexGramSchmidt.Conformance
import HexGramSchmidt.GramDet
import HexGramSchmidt.Rat
import HexGramSchmidt.Update

/-!
Gram-Schmidt scaffolding.

This root module re-exports the scaffolded integer-input
and rational-input Gram-Schmidt basis, coefficient, and
Gram-determinant declarations, together with the integer
scaled-coefficient and row-operation update surface that downstream
LLL work will build on.
-/

namespace HexGramSchmidt
