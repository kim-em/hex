import HexHensel.Linear

/-!
Executable multifactor Hensel lifting surface.

This module exposes the ordered product convention used by downstream
factorization code and implements a sequential multifactor lift by repeatedly
reducing the problem to the binary Hensel lift.
-/

namespace Array

/-- Ordered product of integer polynomial factors, using left-fold order. -/
def polyProduct (factors : Array Hex.ZPoly) : Hex.ZPoly :=
  factors.foldl (· * ·) 1

end Array

namespace Hex

namespace ZPoly

private def multifactorLiftList
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Array ZPoly
  | [] => #[]
  | [_g] => #[reduceModPow f p k]
  | g :: rest =>
      let restFactors := rest.toArray
      let h := Array.polyProduct restFactors
      let xgcd := DensePoly.xgcd (modP p g) (modP p h)
      let lifted := henselLift p k f g h xgcd.left xgcd.right
      #[lifted.g] ++ multifactorLiftList p k lifted.h rest

/--
Lift an ordered array of factors from congruence modulo `p` to congruence
modulo `p^k`.
-/
def multifactorLift
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  multifactorLiftList p k f factors.toList

/-- The product of the lifted factors is congruent to `f` modulo `p^k`. -/
theorem multifactorLift_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hprod : ZPoly.congr (Array.polyProduct factors) f p) :
    ZPoly.congr (Array.polyProduct (multifactorLift p k f factors)) f (p ^ k) := by
  sorry

end ZPoly

end Hex
