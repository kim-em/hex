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

private def quadraticModulus (m : Nat) : Nat :=
  m * m

private def canonicalMod (z : Int) (modulus : Nat) : Int :=
  Int.ofNat <| Int.toNat (z % Int.ofNat modulus)

private def reduceCoeffModSquare (z : Int) (m : Nat) : Int :=
  canonicalMod z (quadraticModulus m)

private def addModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (f + g) m

private def subModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  QuadraticLiftResult.reduceModSquare (f - g) m

private def mulModSquare (f g : ZPoly) (m : Nat) : ZPoly :=
  if f.isZero || g.isZero then
    0
  else
    let modulus := quadraticModulus m
    let fCoeffs := (Array.range f.size).map fun i => canonicalMod (f.coeff i) modulus
    let gCoeffs := (Array.range g.size).map fun j => canonicalMod (g.coeff j) modulus
    let coeffs := Id.run do
      let mut acc := Array.replicate (f.size + g.size - 1) (0 : Int)
      for i in [0:f.size] do
        let fi := fCoeffs.getD i 0
        for j in [0:g.size] do
          let k := i + j
          let next := acc.getD k 0 + fi * gCoeffs.getD j 0
          acc := acc.set! k (canonicalMod next modulus)
      return acc
    DensePoly.ofCoeffs coeffs

-- The Hensel theorem surface supplies monic divisors; this executable helper
-- uses that invariant to avoid coefficient division in the modular hot path.
private def divModMonicModSquareAux
    (m : Nat) (q : ZPoly) : Nat → ZPoly → ZPoly → ZPoly × ZPoly
  | 0, quot, rem => (quot, rem)
  | fuel + 1, quot, rem =>
      if q.isZero then
        (0, QuadraticLiftResult.reduceModSquare rem m)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let coeff := reduceCoeffModSquare rem.leadingCoeff m
              let term := DensePoly.monomial k coeff
              let quot := addModSquare quot term m
              let rem := subModSquare rem (mulModSquare term q m) m
              divModMonicModSquareAux m q fuel quot rem
        | _, _ => (quot, rem)

private def divModMonicModSquare (p q : ZPoly) (m : Nat) : ZPoly × ZPoly :=
  let p := QuadraticLiftResult.reduceModSquare p m
  divModMonicModSquareAux m q p.size 0 p

/-- One quadratic Hensel correction step from modulus `m` to modulus `m^2`. -/
def quadraticHenselStep
    (m : Nat) (f g h s t : ZPoly) : QuadraticLiftResult :=
  let e := QuadraticLiftResult.factorError f g h
  let te := mulModSquare t e m
  let factorQR := divModMonicModSquare te g m
  let qFactor := factorQR.1
  let rFactor := factorQR.2
  let g' := addModSquare g rFactor m
  let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
  let h' := addModSquare h hCorrection m
  let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
  let tb := mulModSquare t b m
  let bezoutQR := divModMonicModSquare tb g' m
  let qBezout := bezoutQR.1
  let rBezout := bezoutQR.2
  let t' := subModSquare t rBezout m
  let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
  { g := g', h := h', s := s', t := t' }

private theorem quadraticHenselStep_raw_factor_congr
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 0 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    ZPoly.congr (g' * h') f (m * m) := by
  sorry

private theorem quadraticHenselStep_bezout_error_congr_zero
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
    ZPoly.congr b 0 m := by
  sorry

private theorem quadraticHenselStep_bezout_correction_congr
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
    let tb := mulModSquare t b m
    let bezoutQR := divModMonicModSquare tb g' m
    let qBezout := bezoutQR.1
    let rBezout := bezoutQR.2
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') (1 - b * b) (m * m) := by
  sorry

private theorem congr_one_sub_square_of_congr_zero
    (m : Nat) (b : ZPoly)
    (hm : 1 < m)
    (hb : ZPoly.congr b 0 m) :
    ZPoly.congr (1 - b * b) 1 (m * m) := by
  sorry

private theorem quadraticHenselStep_raw_bezout_congr
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let qFactor := factorQR.1
    let rFactor := factorQR.2
    let g' := addModSquare g rFactor m
    let hCorrection := addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m
    let h' := addModSquare h hCorrection m
    let b := subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m
    let tb := mulModSquare t b m
    let bezoutQR := divModMonicModSquare tb g' m
    let qBezout := bezoutQR.1
    let rBezout := bezoutQR.2
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') 1 (m * m) := by
  intro e te factorQR qFactor rFactor g' hCorrection h' b tb bezoutQR qBezout rBezout t' s'
  have hb : ZPoly.congr b 0 m := by
    simpa [e, te, factorQR, qFactor, rFactor, g', hCorrection, h'] using
      quadraticHenselStep_bezout_error_congr_zero m f g h s t hm hprod hbez hmonic
  exact ZPoly.congr_trans
    (s' * g' + t' * h')
    (1 - b * b)
    1
    (m * m)
    (by
      simpa [e, te, factorQR, qFactor, rFactor, g', hCorrection, h', b, tb,
        bezoutQR, qBezout, rBezout, t', s'] using
        quadraticHenselStep_bezout_correction_congr m f g h s t hm hprod hbez hmonic)
    (congr_one_sub_square_of_congr_zero m b hm hb)

private theorem quadraticHenselStep_g_update_monic
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hmonic : DensePoly.Monic g) :
    let e := QuadraticLiftResult.factorError f g h
    let te := mulModSquare t e m
    let factorQR := divModMonicModSquare te g m
    let rFactor := factorQR.2
    DensePoly.Monic (addModSquare g rFactor m) := by
  sorry

/-- The updated factors multiply to `f` modulo `m^2`. -/
theorem quadraticHenselStep_factor_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 0 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.g * r.h) f (m * m) := by
  unfold quadraticHenselStep
  exact quadraticHenselStep_raw_factor_congr m f g h s t hm hprod hbez hmonic

/-- The updated Bezout witnesses certify coprimality modulo `m^2`. -/
theorem quadraticHenselStep_bezout_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.s * r.g + r.t * r.h) 1 (m * m) := by
  unfold quadraticHenselStep
  exact quadraticHenselStep_raw_bezout_congr m f g h s t hm hprod hbez hmonic

/-- The quadratic step lifts both factor and Bezout congruences to modulus `m^2`. -/
theorem quadraticHenselStep_spec
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : DensePoly.Monic g) :
    let r := quadraticHenselStep m f g h s t
    ZPoly.congr (r.g * r.h) f (m * m) ∧
      ZPoly.congr (r.s * r.g + r.t * r.h) 1 (m * m) := by
  exact
    ⟨quadraticHenselStep_factor_spec m f g h s t (Nat.lt_trans Nat.zero_lt_one hm)
        hprod hbez hmonic,
      quadraticHenselStep_bezout_spec m f g h s t hm hprod hbez hmonic⟩

/-- The monic factor remains monic after the quadratic correction. -/
theorem quadraticHenselStep_monic
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hmonic : DensePoly.Monic g) :
    DensePoly.Monic (quadraticHenselStep m f g h s t).g := by
  unfold quadraticHenselStep
  exact quadraticHenselStep_g_update_monic m f g h s t hm hmonic

end ZPoly
end Hex
