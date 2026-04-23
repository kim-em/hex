import HexHensel.Linear

/-!
Executable multifactor Hensel-lifting scaffolding.

This module fixes the public ordered-array API promised by the
`hex-hensel` spec. It introduces the shared `Array.polyProduct`
convention for `ZPoly` factors together with a total `multifactorLift`
placeholder that preserves the external list-shaped contract while later
phases fill in the internal lifting algorithm.
-/

open HexPolyZ

namespace Array

/--
Ordered product convention for multifactor Hensel lifting.

The public contract is the left fold of multiplication with identity `1`
on the input array order.
-/
def polyProduct (factors : Array ZPoly) : ZPoly :=
  factors.foldl (init := HexPoly.DensePoly.C (R := Int) 1) (· * ·)

end Array

namespace HexHensel

/--
Phase 1 multifactor-lifting scaffold.

The executable implementation is introduced in later phases; for now the
scaffold preserves the ordered-array interface required by downstream
factorization code.
-/
def multifactorLift (p k : Nat) (f : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  let _ := p
  let _ := k
  let _ := f
  factors

/--
If the input ordered product matches `f` modulo `p`, then the lifted
ordered product matches `f` modulo `p^k`.
-/
theorem multifactorLift_spec
    (p k : Nat) (f : ZPoly) (factors : Array ZPoly)
    (hprod : ZPoly.congr (Array.polyProduct factors) f p) :
    ZPoly.congr (Array.polyProduct (multifactorLift p k f factors)) f (p ^ k) := by
  sorry

end HexHensel
