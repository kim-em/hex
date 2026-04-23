import HexGF2.GF2n

/-!
Mathlib bridge entrypoint for the small-word `GF2n` carrier.

The executable `HexGF2.GF2n` module now owns the direct small-word
`Fintype` and `Field` scaffold promised by the spec. This bridge file
remains as the stable import path for later equivalence theorems and
other Mathlib-facing lemmas.
-/

namespace HexGF2

namespace GF2n

end GF2n

end HexGF2
