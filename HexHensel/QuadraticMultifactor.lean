import HexHensel.Multifactor
import HexHensel.Quadratic

/-!
Quadratic multifactor Hensel lifting (Phase 1 scaffolding).

This module exposes `multifactorLiftQuadratic`, the production multifactor
Hensel lifter named on equal footing with `multifactorLift` in
`hex-hensel`. The implementation reuses the per-step quadratic primitive
`quadraticHenselStep` inside a sequential split tree that mirrors
`multifactorLift`. Iteration to the requested precision `p^k` is handled
by a doubling loop on the Bezout-witnessed `QuadraticLiftResult`.

Phase 1 deliverable: type signatures and an executable surface; the
spec proof is left as a single `sorry` (see `multifactorLiftQuadratic_spec`).
The linear-vs-quadratic agreement obligation lives in
`hex-hensel-mathlib`.
-/

namespace Hex

namespace ZPoly

/-- Iterate `quadraticHenselStep` on a Bezout-witnessed factorisation,
doubling the modulus exponent each time. The first index is the current
modulus exponent; the second is the number of remaining doubling steps. -/
private def iterateQuadraticHensel
    (p : Nat) [ZMod64.Bounds p] (f : ZPoly) :
    Nat → Nat → QuadraticLiftResult → QuadraticLiftResult
  | _current, 0, acc => acc
  | current, fuel + 1, acc =>
      let m := p ^ current
      let next := quadraticHenselStep m f acc.g acc.h acc.s acc.t
      iterateQuadraticHensel p f (2 * current) fuel next

/-- Lift a Bezout-witnessed factorisation modulo `p` to one valid modulo
`p^k` by iterating `quadraticHenselStep`.

`k` doubling steps starting from modulus `p` reach modulus `p^(2^k)`,
which dominates `p^k` for all `k`; the final result is reduced modulo
`p^k` to expose the requested precision. -/
def henselLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h s t : ZPoly) : QuadraticLiftResult :=
  let init : QuadraticLiftResult := { g, h, s, t }
  let lifted := iterateQuadraticHensel p f 1 k init
  { g := ZPoly.reduceModPow lifted.g p k
    h := ZPoly.reduceModPow lifted.h p k
    s := ZPoly.reduceModPow lifted.s p k
    t := ZPoly.reduceModPow lifted.t p k }

private def multifactorLiftQuadraticList
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) : List ZPoly → Array ZPoly
  | [] => #[]
  | [_g] => #[ZPoly.reduceModPow f p k]
  | g :: rest =>
      let restFactors := rest.toArray
      let h := Array.polyProduct restFactors
      let xgcd := ZPoly.normalizedXGCD p g h
      let s := FpPoly.liftToZ xgcd.left
      let t := FpPoly.liftToZ xgcd.right
      let lifted := henselLiftQuadratic p k f g h s t
      #[lifted.g] ++ multifactorLiftQuadraticList p k lifted.h rest

/--
Quadratic multifactor Hensel lift.

Lifts an ordered array of factors of `f` from congruence modulo `p` to
congruence modulo `p^k` using the doubling step `quadraticHenselStep`
inside the same sequential split tree as `multifactorLift`.
-/
def multifactorLiftQuadratic
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly) : Array ZPoly :=
  multifactorLiftQuadraticList p k f factors.toList

/--
The product of the lifted factors is congruent to `f` modulo `p^k`,
under the same recursive precondition package consumed by
`multifactorLift_spec`.

Phase 1: the proof is deferred. The lift-uniqueness companion
(linear-vs-quadratic agreement after canonicalisation) lives in
`hex-hensel-mathlib`.
-/
theorem multifactorLiftQuadratic_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : Array ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : MultifactorLiftInvariant p k f factors.toList) :
    ZPoly.congr (Array.polyProduct (multifactorLiftQuadratic p k f factors))
      f (p ^ k) := by
  sorry

end ZPoly

end Hex
