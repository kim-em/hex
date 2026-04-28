import HexHensel.Basic

/-!
Executable quadratic Hensel lifting.

This module implements the doubling step that lifts a factorization and its
Bezout witnesses from congruence modulo `m` to congruence modulo `m * m`,
together with the initial theorem surface describing the updated invariants.
-/
namespace Hex

/-- Result of one quadratic Hensel lift step. -/
structure QuadraticLiftResult where
  g : ZPoly
  h : ZPoly
  s : ZPoly
  t : ZPoly

namespace QuadraticLiftResult

/-- Canonical coefficient reduction modulo `m^2`. -/
def reduceModSquare (f : ZPoly) (m : Nat) : ZPoly :=
  ZPoly.reduceModPow f m 2

/-- The factor error corrected during the quadratic Hensel step. -/
def factorError (f g h : ZPoly) : ZPoly :=
  f - g * h

/-- The Bezout error corrected after the factor update. -/
def bezoutError (g h s t : ZPoly) : ZPoly :=
  s * g + t * h - 1

end QuadraticLiftResult

namespace ZPoly

/-- One quadratic Hensel correction step from modulus `m` to modulus `m^2`. -/
def quadraticHenselStep
    (m : Nat) (f g h s t : ZPoly) : QuadraticLiftResult :=
  let e := QuadraticLiftResult.factorError f g h
  let te := QuadraticLiftResult.reduceModSquare (t * e) m
  let factorQR := DensePoly.divMod te g
  let qFactor := factorQR.1
  let rFactor := factorQR.2
  let g' := QuadraticLiftResult.reduceModSquare (g + rFactor) m
  let hCorrection := s * e + qFactor * h
  let h' := QuadraticLiftResult.reduceModSquare (h + hCorrection) m
  let b := QuadraticLiftResult.bezoutError g' h' s t
  let tb := QuadraticLiftResult.reduceModSquare (t * b) m
  let bezoutQR := DensePoly.divMod tb g'
  let qBezout := bezoutQR.1
  let rBezout := bezoutQR.2
  let t' := QuadraticLiftResult.reduceModSquare (t - rBezout) m
  let s' := QuadraticLiftResult.reduceModSquare (s - s * b - qBezout * h') m
  { g := g', h := h', s := s', t := t' }

/-- The updated factors multiply to `f` modulo `m^2`. -/
theorem quadraticHenselStep_factor_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.g * r.h) f (m * m) := by
  sorry

/-- The updated Bezout witnesses certify coprimality modulo `m^2`. -/
theorem quadraticHenselStep_bezout_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.s * r.g + r.t * r.h) 1 (m * m) := by
  sorry

/-- The quadratic step lifts both factor and Bezout congruences to modulus `m^2`. -/
theorem quadraticHenselStep_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.g * r.h) f (m * m) ∧
      ZPoly.congr (r.s * r.g + r.t * r.h) 1 (m * m) := by
  sorry

/-- The monic factor remains monic after the quadratic correction. -/
theorem quadraticHenselStep_monic
    (m : Nat)
    (f g h s t : ZPoly)
    (hmonic : DensePoly.Monic g) :
    DensePoly.Monic (quadraticHenselStep m f g h s t).g := by
  sorry

end ZPoly
end Hex
