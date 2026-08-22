module

public import HexBasic
public import HexPoly
public import HexPolyMathlib
public import HexMvPoly
public import HexMvPolyMathlib
public import HexMatrix
public import HexMatrixMathlib
public import HexGramSchmidt
public import HexGramSchmidtMathlib
public import HexLLL
public import HexLLLMathlib
public import HexPolyFpMathlib
public import HexConway
public import HexGFqField
public import HexGF2
public import HexGF2Mathlib
public import HexGFq
public import HexGFqMathlib
public import HexCharPoly
public import HexCharPolyMathlib

public section

/-!
`Hex` — convenience aggregator for the released hex libraries.

Requiring `hex` pulls in every released executable core and Mathlib
correspondence layer at a single coherent pinned set. `import Hex` re-exports
all of them; or import an individual library directly. To depend on just a
Mathlib-free computational package, require that package (for example
`hex-mv-poly` or `hex-lll`) instead of `hex`.
-/
