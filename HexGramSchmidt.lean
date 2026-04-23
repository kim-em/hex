import HexGramSchmidt.Int
import HexGramSchmidt.Conformance
import HexGramSchmidt.GramDet
import HexGramSchmidt.Rat
import HexGramSchmidt.Update

/-!
Gram-Schmidt scaffolding.

This root module re-exports the scaffolded integer-input Gram-Schmidt
basis, coefficient, Gram-determinant, and row-operation surface,
together with the executable rational-input Gram-determinant helper
used by downstream LLL work.
-/

namespace HexGramSchmidt
