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

/--
Recursive preconditions required by the sequential multifactor lift.

Each nontrivial split must supply exactly the invariant package consumed by
`henselLift_spec`, and the recursive tail must satisfy the same contract for
the lifted complementary factor.
-/
def MultifactorLiftInvariant
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Prop
  | [] => ZPoly.congr 1 f (p ^ k)
  | [_g] => True
  | g :: rest =>
      let h := Array.polyProduct rest.toArray
      let xgcd := DensePoly.xgcd (modP p g) (modP p h)
      let lifted := henselLift p k f g h xgcd.left xgcd.right
      LinearLiftLoopInvariant p 1 f xgcd.left xgcd.right
        { g := reduceModPow g p 1
          h := reduceModPow h p 1 } ∧
        (∀ (n : Nat) (state : LinearLiftResult),
          1 ≤ n →
          LinearLiftLoopInvariant p n f xgcd.left xgcd.right state →
          LinearLiftStepDegreeInvariant p n f xgcd.left xgcd.right state) ∧
        (∀ (n : Nat) (state : LinearLiftResult),
          1 ≤ n →
          LinearLiftLoopInvariant p n f xgcd.left xgcd.right state →
          let next := linearHenselStep p n f state.g state.h xgcd.left xgcd.right
          ZPoly.congr
            (FpPoly.liftToZ
              (xgcd.left * ZPoly.modP p next.g + xgcd.right * ZPoly.modP p next.h))
            1 p) ∧
        MultifactorLiftInvariant p k lifted.h rest

private theorem multifactorLiftList_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : MultifactorLiftInvariant p k f factors) :
    ZPoly.congr (Array.polyProduct (multifactorLiftList p k f factors)) f (p ^ k) := by
  sorry

/--
The product of the lifted factors is congruent to `f` modulo `p^k`, provided
each recursive binary split supplies the linear Hensel invariant package.
-/
theorem multifactorLift_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : MultifactorLiftInvariant p k f factors.toList) :
    ZPoly.congr (Array.polyProduct (multifactorLift p k f factors)) f (p ^ k) := by
  simpa [multifactorLift] using
    multifactorLiftList_spec p k f factors.toList hk hp hinv

end ZPoly

end Hex
