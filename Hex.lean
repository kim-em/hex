module

public import HexBasic
public import HexArith
public import HexPrimality
public import HexPrimalityMathlib
public import HexPoly
public import HexMvPoly
public import HexModArith
public import HexSparsePoly
public import HexPolyMathlib
public import HexSparsePolyMathlib
public import HexMvPolyMathlib
public import HexPolyFp
public import HexPolyZ
public import HexModArithMathlib
public import HexPolyFpMathlib
public import HexGFqRing
public import HexHensel
public import HexPolyZMathlib
public import HexHenselMathlib
public import HexRoots
public import HexRealRoots
public import HexRootsMathlib
public import HexRealRootsMathlib
public import HexMatrix
public import HexRowReduce
public import HexBerlekamp
public import HexConway
public import HexGFqField
public import HexGF2
public import HexGF2Mathlib
public import HexGFq
public import HexGFqMathlib
public import HexDeterminant
public import HexBareiss
public import HexMatrixMathlib
public import HexRowReduceMathlib
public import HexDeterminantMathlib
public import HexBareissMathlib
public import HexBerlekampMathlib
public import HexGramSchmidt
public import HexGramSchmidtMathlib
public import HexLLL
public import HexBerlekampZassenhaus
public import HexLLLMathlib
public import HexBerlekampZassenhausMathlib
public import HexGraphIso
public import HexGraphIsoMathlib
public import HexResultant
public import HexResultantMathlib
public import HexNumberField
public import HexNumberFieldMathlib
public import HexNumberFieldTower
public import HexNumberFieldTowerMathlib
public import HexRCF

public section

/-!
`Hex` — convenience aggregator for the released hex libraries.

Requiring `hex` pulls in every released executable core and Mathlib
correspondence layer at a single coherent pinned set. `import Hex` re-exports
all of them; or import an individual library directly. To depend on just a
Mathlib-free computational package, require that package (for example
`hex-mv-poly` or `hex-lll`) instead of `hex`.
-/
