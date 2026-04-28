import HexHensel.Basic

/-!
Executable single-step linear Hensel lifting.

This module implements the linear correction step that lifts a factorization
from congruence modulo `p^k` to congruence modulo `p^(k+1)`, together with the
initial theorem surface describing its computational invariants.
-/
namespace Hex

namespace ZPoly

/-- Divide every coefficient by `m` using Lean's truncating integer division. -/
def coeffwiseDiv (f : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => f.coeff i / Int.ofNat m) |>.toArray

@[simp] theorem coeff_coeffwiseDiv (f : ZPoly) (m i : Nat) :
    (coeffwiseDiv f m).coeff i = f.coeff i / Int.ofNat m := by
  sorry

end ZPoly

/-- Result of one linear Hensel lift step. -/
structure LinearLiftResult where
  g : ZPoly
  h : ZPoly

namespace LinearLiftResult

/-- The lifted-and-scaled increment used by one linear Hensel step. -/
def liftScaledIncrement (p k : Nat) [ZMod64.Bounds p] (r : FpPoly p) : ZPoly :=
  DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ r)

end LinearLiftResult

namespace ZPoly

/-- One linear Hensel correction step from modulus `p^k` to `p^(k+1)`. -/
def linearHenselStep
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p) : LinearLiftResult :=
  let e := coeffwiseDiv (f - g * h) (p ^ k)
  let gMod := modP p g
  let hMod := modP p h
  let eMod := modP p e
  let qr := DensePoly.divMod (t * eMod) gMod
  let q := qr.1
  let r := qr.2
  let g' := g + LinearLiftResult.liftScaledIncrement p k r
  let hCorrection := s * eMod + q * hMod
  let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
  { g := reduceModPow g' p (k + 1)
    h := reduceModPow h' p (k + 1) }

private def henselLiftLoop
    (p : Nat) [ZMod64.Bounds p]
    (steps current : Nat)
    (f : ZPoly) (s t : FpPoly p)
    (acc : LinearLiftResult) : LinearLiftResult :=
  match steps with
  | 0 => acc
  | steps + 1 =>
      let next := linearHenselStep p current f acc.g acc.h s t
      henselLiftLoop p steps (current + 1) f s t next

/--
Lift a factorization modulo `p` to a factorization modulo `p^k` by iterating the
linear Hensel step.
-/
def henselLift
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p) : LinearLiftResult :=
  match k with
  | 0 =>
      { g := reduceModPow g p 0
        h := reduceModPow h p 0 }
  | k' + 1 =>
      let start :=
        { g := reduceModPow g p 1
          h := reduceModPow h p 1 }
      henselLiftLoop p k' 1 f s t start

/-- The lifted factors still multiply to `f` modulo the next power of `p`. -/
theorem linearHenselStep_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hbez :
      ZPoly.congr
        (FpPoly.liftToZ (s * ZPoly.modP p g + t * ZPoly.modP p h))
        1 p)
    (hmonic : DensePoly.Monic g) :
    let r := linearHenselStep p k f g h s t
    ZPoly.congr (r.g * r.h) f (p ^ (k + 1)) := by
  sorry

/-- The linear step preserves monicity of the lifted `g` factor. -/
theorem linearHenselStep_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hmonic : DensePoly.Monic g) :
    DensePoly.Monic (linearHenselStep p k f g h s t).g := by
  sorry

/-- The linear step preserves the degree of the monic `g` factor. -/
theorem linearHenselStep_g_degree?_eq
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hmonic : DensePoly.Monic g) :
    (linearHenselStep p k f g h s t).g.degree? = g.degree? := by
  sorry

/-- The linear step keeps the degree of `h` unchanged under the expected invariant. -/
theorem linearHenselStep_h_degree?_eq
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hprod : ZPoly.congr (g * h) f (p ^ k)) :
    (linearHenselStep p k f g h s t).h.degree? = h.degree? := by
  sorry

/-- The iterative linear wrapper lifts the factorization to congruence modulo `p^k`. -/
theorem henselLift_spec
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f p)
    (hbez :
      ZPoly.congr
        (FpPoly.liftToZ (s * ZPoly.modP p g + t * ZPoly.modP p h))
        1 p)
    (hmonic : DensePoly.Monic g) :
    let r := henselLift p k f g h s t
    ZPoly.congr (r.g * r.h) f (p ^ k) := by
  sorry

/-- The iterative linear wrapper preserves monicity of the lifted `g` factor. -/
theorem henselLift_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hmonic : DensePoly.Monic g) :
    DensePoly.Monic (henselLift p k f g h s t).g := by
  sorry

end ZPoly
end Hex
