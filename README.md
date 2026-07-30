# hex

Verified computational algebra in Lean 4: an aggregator for the released
`hex` libraries.

- Manual: <https://kim-em.github.io/hex-dev/>
- API documentation: <https://leanprover.github.io/hex/docs>

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex"
git = "https://github.com/leanprover/hex.git"
rev = "main"
```

Then `import Hex` re-exports every library in the table below at a single
coherent pinned set:

```lean
import Hex

open Hex

-- Exact, fraction-free integer determinant.
def M : Matrix Int 3 3 := #m[2, 1, 1; 1, 2, 1; 1, 1, 2]
#eval M.det   -- 4

-- LLL: reduce an integer lattice basis and read off a provably short vector.
-- The `by decide` arguments discharge the reduction-factor side conditions.
def L : Matrix Int 3 3 := #m[1, 1, 1; 1, 0, 2; 3, 5, 6]
#eval lllNative.firstShortVector L (3 / 4) (by decide +kernel) (by decide +kernel) (by decide)
```

To depend on just one piece, require that library directly (for example
[`hex-lll`](https://github.com/leanprover/hex-lll) for the Mathlib-free LLL
core) instead of the aggregator.

# Libraries

Each computational library is Mathlib-free; its Mathlib correspondence proofs
and Mathlib-facing API, where they exist, live in a separate `*-mathlib`
library.

| Component | Computational | Mathlib layer |
|---|---|---|
| Foundations | [HexBasic](https://github.com/leanprover/hex-basic) | — |
| Dense polynomials | [HexPoly](https://github.com/leanprover/hex-poly) | [HexPolyMathlib](https://github.com/leanprover/hex-poly-mathlib) |
| Multivariate polynomials | [HexMvPoly](https://github.com/leanprover/hex-mv-poly) | [HexMvPolyMathlib](https://github.com/leanprover/hex-mv-poly-mathlib) |
| Matrices | [HexMatrix](https://github.com/leanprover/hex-matrix) | [HexMatrixMathlib](https://github.com/leanprover/hex-matrix-mathlib) |
| Row reduction | [HexRowReduce](https://github.com/leanprover/hex-row-reduce) | [HexRowReduceMathlib](https://github.com/leanprover/hex-row-reduce-mathlib) |
| Determinants | [HexDeterminant](https://github.com/leanprover/hex-determinant) | [HexDeterminantMathlib](https://github.com/leanprover/hex-determinant-mathlib) |
| Bareiss | [HexBareiss](https://github.com/leanprover/hex-bareiss) | [HexBareissMathlib](https://github.com/leanprover/hex-bareiss-mathlib) |
| Gram-Schmidt | [HexGramSchmidt](https://github.com/leanprover/hex-gram-schmidt) | [HexGramSchmidtMathlib](https://github.com/leanprover/hex-gram-schmidt-mathlib) |
| LLL | [HexLLL](https://github.com/leanprover/hex-lll) | [HexLLLMathlib](https://github.com/leanprover/hex-lll-mathlib) |

Development of the full project (including unreleased libraries) happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo.
