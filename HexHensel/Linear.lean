import HexHensel.Basic

/-!
Executable single-step linear Hensel lifting.

This module implements the linear correction step that lifts a factorization
from congruence modulo `p^k` to congruence modulo `p^(k+1)`, together with the
initial theorem surface describing its computational invariants.
-/
namespace Hex

private theorem list_getD_map_range {α : Type} [Zero α] (size n : Nat) (f : Nat → α) :
    ((List.range size).map f).getD n (Zero.zero : α) =
      if n < size then f n else (Zero.zero : α) := by
  by_cases hn : n < size
  · simp [hn, List.getD]
  · simp [hn, List.getD]

namespace ZPoly

/-- Divide every coefficient by `m` using Lean's truncating integer division. -/
def coeffwiseDiv (f : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range f.size).map (fun i => f.coeff i / Int.ofNat m) |>.toArray

@[simp] theorem coeff_coeffwiseDiv (f : ZPoly) (m i : Nat) :
    (coeffwiseDiv f m).coeff i = f.coeff i / Int.ofNat m := by
  unfold coeffwiseDiv
  rw [DensePoly.coeff_ofCoeffs_list]
  rw [list_getD_map_range]
  by_cases hi : i < f.size
  · simp [hi]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hi)
    simp [hi, hcoeff]
    rfl

private theorem scale_coeffwiseDiv_sub_of_congr
    (f g : ZPoly) (m : Nat) (hfg : ZPoly.congr g f m) :
    DensePoly.scale (Int.ofNat m) (coeffwiseDiv (f - g) m) = f - g := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_scale]
  · rw [coeff_coeffwiseDiv]
    rw [DensePoly.coeff_sub]
    · have hdvd_gf : (m : Int) ∣ g.coeff i - f.coeff i :=
        Int.dvd_of_emod_eq_zero (hfg i)
      have hdvd : (m : Int) ∣ f.coeff i - g.coeff i := by
        rw [← Int.neg_sub]
        exact Int.dvd_neg.mpr hdvd_gf
      rw [Int.mul_comm]
      exact Int.ediv_mul_cancel hdvd
    · rfl
  · exact Int.mul_zero _

end ZPoly

/-- Result of one linear Hensel lift step. -/
structure LinearLiftResult where
  g : ZPoly
  h : ZPoly

namespace LinearLiftResult

/-- The lifted-and-scaled increment used by one linear Hensel step. -/
def liftScaledIncrement (p k : Nat) [ZMod64.Bounds p] (r : FpPoly p) : ZPoly :=
  DensePoly.scale (Int.ofNat (p ^ k)) (FpPoly.liftToZ r)

@[simp] theorem coeff_liftScaledIncrement
    (p k : Nat) [ZMod64.Bounds p] (r : FpPoly p) (i : Nat) :
    (liftScaledIncrement p k r).coeff i =
      Int.ofNat (p ^ k) * Int.ofNat (r.coeff i).toNat := by
  unfold liftScaledIncrement
  rw [DensePoly.coeff_scale]
  · rw [FpPoly.coeff_liftToZ]
  · exact Int.mul_zero _

/-- A scaled lift is coefficientwise zero modulo the scaling modulus. -/
theorem congr_liftScaledIncrement_zero
    (p k : Nat) [ZMod64.Bounds p] (r : FpPoly p) :
    ZPoly.congr (liftScaledIncrement p k r) 0 (p ^ k) := by
  intro i
  rw [coeff_liftScaledIncrement]
  rw [DensePoly.coeff_zero]
  simp

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

private theorem congr_mul_reduceModPow_pair
    (p k : Nat) [ZMod64.Bounds p] (g h : ZPoly) :
    ZPoly.congr
      (ZPoly.reduceModPow g p k * ZPoly.reduceModPow h p k)
      (g * h)
      (p ^ k) := by
  apply ZPoly.congr_mul
  · exact ZPoly.congr_reduceModPow g p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
  · exact ZPoly.congr_reduceModPow h p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))

private theorem linearHenselStep_correction_identity
    (p : Nat) [ZMod64.Bounds p]
    (gMod hMod eMod s t q r : FpPoly p)
    (hdiv : q * gMod + r = t * eMod)
    (hbez : s * gMod + t * hMod = 1) :
    r * hMod + gMod * (s * eMod + q * hMod) = eMod := by
  calc
    r * hMod + gMod * (s * eMod + q * hMod)
        = r * hMod + (gMod * (s * eMod) + gMod * (q * hMod)) := by
          rw [FpPoly.left_distrib]
    _ = (s * gMod) * eMod + (q * gMod + r) * hMod := by
          grind [FpPoly.add_assoc, FpPoly.add_comm, FpPoly.mul_assoc, FpPoly.mul_comm,
            FpPoly.right_distrib]
    _ = (s * gMod) * eMod + (t * eMod) * hMod := by
          rw [hdiv]
    _ = (s * gMod) * eMod + (t * hMod) * eMod := by
          grind [FpPoly.mul_assoc, FpPoly.mul_comm]
    _ = (s * gMod + t * hMod) * eMod := by
          rw [FpPoly.right_distrib]
    _ = 1 * eMod := by
          rw [hbez]
    _ = eMod := by
          rw [FpPoly.one_mul]

private theorem modP_one (p : Nat) [ZMod64.Bounds p] :
    ZPoly.modP p (1 : ZPoly) = (1 : FpPoly p) := by
  have hcong : ZPoly.congr (FpPoly.liftToZ (1 : FpPoly p)) (1 : ZPoly) p := by
    intro i
    rw [FpPoly.coeff_liftToZ]
    change
      (Int.ofNat (DensePoly.coeff (DensePoly.C (1 : ZMod64 p)) i).toNat -
          DensePoly.coeff (DensePoly.C (1 : Int)) i) % (p : Int) = 0
    rw [DensePoly.coeff_C, DensePoly.coeff_C]
    cases i with
    | zero =>
        cases p with
        | zero =>
            cases Nat.not_lt_zero _ (ZMod64.Bounds.pPos (p := 0))
        | succ p' =>
            cases p' with
            | zero =>
                change (Int.ofNat (1 % 1) - 1) % (1 : Int) = 0
                simp
            | succ p'' =>
                have hlt : 1 < Nat.succ (Nat.succ p'') := by omega
                change
                  (Int.ofNat (1 % Nat.succ (Nat.succ p'')) - 1) %
                    (Nat.succ (Nat.succ p'') : Int) = 0
                simp [Nat.mod_eq_of_lt hlt]
    | succ i =>
        change (Int.ofNat 0 - (0 : Int)) % (p : Int) = 0
        simp
  exact Eq.trans (ZPoly.modP_eq_of_congr p _ _ (ZPoly.congr_symm _ _ _ hcong))
    (FpPoly.modP_liftToZ (p := p) (1 : FpPoly p))

private theorem congr_liftToZ_of_modP_eq
    (p : Nat) [ZMod64.Bounds p] (u : FpPoly p) (z : ZPoly)
    (h : ZPoly.modP p z = u) :
    ZPoly.congr (FpPoly.liftToZ u) z p := by
  simpa [← h] using FpPoly.congr_liftToZ_modP (p := p) z

private theorem modP_add_lift_mul
    (p : Nat) [ZMod64.Bounds p] (g h : ZPoly) (r hCorrection : FpPoly p) :
    ZPoly.modP p (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection) =
      r * ZPoly.modP p h + ZPoly.modP p g * hCorrection := by
  sorry

private theorem scale_congr_of_congr_mod_base
    (p k : Nat) (first e : ZPoly)
    (_hk : 1 ≤ k)
    (hfirst : ZPoly.congr first e p) :
    ZPoly.congr
      (DensePoly.scale (Int.ofNat (p ^ k)) first)
      (DensePoly.scale (Int.ofNat (p ^ k)) e)
      (p ^ (k + 1)) := by
  sorry

private theorem linearHenselStep_product_expansion_identity_congr
    (p k : Nat) [ZMod64.Bounds p]
    (g h : ZPoly) (r hCorrection : FpPoly p)
    (_hk : 1 ≤ k) :
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr
      (g' * h')
      (g * h +
        DensePoly.scale (Int.ofNat (p ^ k))
          (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
      (p ^ (k + 1)) := by
  sorry

private theorem linearHenselStep_recombine_error_congr
    (p k : Nat) (f g h : ZPoly) :
    ZPoly.congr (g * h + (f - g * h)) f (p ^ (k + 1)) := by
  intro i
  rw [DensePoly.coeff_add _ _ _ (by rfl), DensePoly.coeff_sub _ _ _ (by rfl)]
  have hzero :
      (g * h).coeff i + (f.coeff i - (g * h).coeff i) - f.coeff i = 0 := by
    omega
  rw [hzero]
  simp

private theorem linearHenselStep_first_order_congr
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (r hCorrection : FpPoly p)
    (hcorr :
      r * ZPoly.modP p h + ZPoly.modP p g * hCorrection =
        ZPoly.modP p (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))) :
    ZPoly.congr
      (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection)
      (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))
      p := by
  have hmod :
      ZPoly.modP p
        (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection) =
        r * ZPoly.modP p h + ZPoly.modP p g * hCorrection :=
    modP_add_lift_mul p g h r hCorrection
  have hlift :
      ZPoly.congr
        (FpPoly.liftToZ (r * ZPoly.modP p h + ZPoly.modP p g * hCorrection))
        (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection)
        p :=
    congr_liftToZ_of_modP_eq p
      (r * ZPoly.modP p h + ZPoly.modP p g * hCorrection)
      (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection)
      hmod
  have he :
      ZPoly.congr
        (FpPoly.liftToZ (ZPoly.modP p (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))))
        (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))
        p :=
    FpPoly.congr_liftToZ_modP
      (p := p) (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))
  have hcorr' :
      ZPoly.congr
        (FpPoly.liftToZ (r * ZPoly.modP p h + ZPoly.modP p g * hCorrection))
        (FpPoly.liftToZ (ZPoly.modP p (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))))
        p := by
    rw [hcorr]
    exact ZPoly.congr_refl _ p
  exact ZPoly.congr_trans _ _ _ p
    (ZPoly.congr_symm _ _ _ hlift)
    (ZPoly.congr_trans _ _ _ p hcorr' he)

private theorem linearHenselStep_scaled_first_order_congr
    (p k : Nat) [ZMod64.Bounds p]
    (f g h first e : ZPoly)
    (_hk : 1 ≤ k)
    (hbase : DensePoly.scale (Int.ofNat (p ^ k)) e = f - g * h)
    (hfirst : ZPoly.congr first e p) :
    ZPoly.congr
      (DensePoly.scale (Int.ofNat (p ^ k)) first)
      (f - g * h)
      (p ^ (k + 1)) := by
  rw [← hbase]
  exact scale_congr_of_congr_mod_base p k first e _hk hfirst

private theorem linearHenselStep_product_expansion_congr
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (r hCorrection : FpPoly p)
    (_hk : 1 ≤ k)
    (_hprod : ZPoly.congr (g * h) f (p ^ k))
    (hfirst :
      ZPoly.congr
        (DensePoly.scale (Int.ofNat (p ^ k))
          (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
        (f - g * h)
        (p ^ (k + 1))) :
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr (g' * h') f (p ^ (k + 1)) := by
  intro g' h'
  have hexpand :
      ZPoly.congr
        (g' * h')
        (g * h +
          DensePoly.scale (Int.ofNat (p ^ k))
            (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
        (p ^ (k + 1)) := by
    simpa [g', h', LinearLiftResult.liftScaledIncrement] using
      linearHenselStep_product_expansion_identity_congr p k g h r hCorrection _hk
  have hsum :
      ZPoly.congr
        (g * h +
          DensePoly.scale (Int.ofNat (p ^ k))
            (FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection))
        (g * h + (f - g * h))
        (p ^ (k + 1)) :=
    ZPoly.congr_add _ _ _ _ _
      (ZPoly.congr_refl (g * h) (p ^ (k + 1))) hfirst
  exact ZPoly.congr_trans _ _ _ _ hexpand
    (ZPoly.congr_trans _ _ _ _
      hsum (linearHenselStep_recombine_error_congr p k f g h))

private theorem linearHenselStep_raw_factor_congr_from_correction
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (r hCorrection _e : FpPoly p)
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hcorr :
      r * ZPoly.modP p h + ZPoly.modP p g * hCorrection =
        ZPoly.modP p (ZPoly.coeffwiseDiv (f - g * h) (p ^ k))) :
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr (g' * h') f (p ^ (k + 1)) := by
  intro g' h'
  let eZ := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
  let first := FpPoly.liftToZ r * h + g * FpPoly.liftToZ hCorrection
  have hbase : DensePoly.scale (Int.ofNat (p ^ k)) eZ = f - g * h := by
    simpa [eZ] using ZPoly.scale_coeffwiseDiv_sub_of_congr f (g * h) (p ^ k) hprod
  have hfirst : ZPoly.congr first eZ p := by
    simpa [first, eZ] using
      linearHenselStep_first_order_congr p k f g h r hCorrection hcorr
  have hscaled :
      ZPoly.congr
        (DensePoly.scale (Int.ofNat (p ^ k)) first)
        (f - g * h)
        (p ^ (k + 1)) :=
    linearHenselStep_scaled_first_order_congr p k f g h first eZ hk hbase hfirst
  simpa [g', h', first] using
    linearHenselStep_product_expansion_congr p k f g h r hCorrection hk hprod hscaled

private theorem linearHenselStep_raw_factor_congr
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hbez :
      ZPoly.congr
        (FpPoly.liftToZ (s * ZPoly.modP p g + t * ZPoly.modP p h))
        1 p)
    (_hmonic : DensePoly.Monic g) :
    let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
    let gMod := ZPoly.modP p g
    let hMod := ZPoly.modP p h
    let eMod := ZPoly.modP p e
    let qr := DensePoly.divMod (t * eMod) gMod
    let q := qr.1
    let r := qr.2
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let hCorrection := s * eMod + q * hMod
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr (g' * h') f (p ^ (k + 1)) := by
  intro e gMod hMod eMod qr q r g' hCorrection h'
  have hdiv : q * gMod + r = t * eMod := by
    simpa [qr, q, r] using DensePoly.divMod_spec (t * eMod) gMod
  have hbezFp : s * gMod + t * hMod = 1 := by
    have hmod := ZPoly.modP_eq_of_congr p _ _ hbez
    rw [FpPoly.modP_liftToZ, modP_one] at hmod
    exact hmod
  have hcorr :
      r * hMod + gMod * hCorrection = eMod := by
    simpa [hCorrection] using
      linearHenselStep_correction_identity p gMod hMod eMod s t q r hdiv hbezFp
  exact
    linearHenselStep_raw_factor_congr_from_correction
      p k f g h r hCorrection eMod hk hprod hcorr

private theorem linearHenselStep_reduced_factor_congr
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hbez :
      ZPoly.congr
        (FpPoly.liftToZ (s * ZPoly.modP p g + t * ZPoly.modP p h))
        1 p)
    (hmonic : DensePoly.Monic g) :
    let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
    let gMod := ZPoly.modP p g
    let hMod := ZPoly.modP p h
    let eMod := ZPoly.modP p e
    let qr := DensePoly.divMod (t * eMod) gMod
    let q := qr.1
    let r := qr.2
    let g' := g + LinearLiftResult.liftScaledIncrement p k r
    let hCorrection := s * eMod + q * hMod
    let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
    ZPoly.congr
      (ZPoly.reduceModPow g' p (k + 1) * ZPoly.reduceModPow h' p (k + 1))
      f
      (p ^ (k + 1)) := by
  intro e gMod hMod eMod qr q r g' hCorrection h'
  exact ZPoly.congr_trans
    (ZPoly.reduceModPow g' p (k + 1) * ZPoly.reduceModPow h' p (k + 1))
    (g' * h')
    f
    (p ^ (k + 1))
    (congr_mul_reduceModPow_pair p (k + 1) g' h')
    (by
      simpa [e, gMod, hMod, eMod, qr, q, r, g', hCorrection, h'] using
        linearHenselStep_raw_factor_congr p k f g h s t hk hprod hbez hmonic)

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
    (hk : 1 ≤ k)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hbez :
      ZPoly.congr
        (FpPoly.liftToZ (s * ZPoly.modP p g + t * ZPoly.modP p h))
        1 p)
    (hmonic : DensePoly.Monic g) :
    let r := linearHenselStep p k f g h s t
    ZPoly.congr (r.g * r.h) f (p ^ (k + 1)) := by
  unfold linearHenselStep
  simpa using
    linearHenselStep_reduced_factor_congr p k f g h s t hk hprod hbez hmonic

/-- The linear step preserves monicity of the lifted `g` factor. -/
theorem linearHenselStep_monic
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hp : 1 < p)
    (hmonic : DensePoly.Monic g)
    (hgCorrectionDegree :
      let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := ZPoly.modP p g
      let eMod := ZPoly.modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      (LinearLiftResult.liftScaledIncrement p k qr.2).degree?.getD 0 < g.degree?.getD 0) :
    DensePoly.Monic (linearHenselStep p k f g h s t).g := by
  sorry

/-- The linear step preserves the degree of the monic `g` factor. -/
theorem linearHenselStep_g_degree?_eq
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hp : 1 < p)
    (hmonic : DensePoly.Monic g)
    (hgCorrectionDegree :
      let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := ZPoly.modP p g
      let eMod := ZPoly.modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      (LinearLiftResult.liftScaledIncrement p k qr.2).degree?.getD 0 < g.degree?.getD 0) :
    (linearHenselStep p k f g h s t).g.degree? = g.degree? := by
  sorry

/-- The linear step keeps the degree of `h` unchanged under the expected invariant. -/
theorem linearHenselStep_h_degree?_eq
    (p k : Nat) [ZMod64.Bounds p]
    (f g h : ZPoly) (s t : FpPoly p)
    (hp : 1 < p)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hhRawDegree :
      let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := ZPoly.modP p g
      let hMod := ZPoly.modP p h
      let eMod := ZPoly.modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      let hCorrection := s * eMod + qr.1 * hMod
      let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
      h'.degree? = h.degree?)
    (hhReducedDegree :
      let e := ZPoly.coeffwiseDiv (f - g * h) (p ^ k)
      let gMod := ZPoly.modP p g
      let hMod := ZPoly.modP p h
      let eMod := ZPoly.modP p e
      let qr := DensePoly.divMod (t * eMod) gMod
      let hCorrection := s * eMod + qr.1 * hMod
      let h' := h + LinearLiftResult.liftScaledIncrement p k hCorrection
      (ZPoly.reduceModPow h' p (k + 1)).degree? = h'.degree?) :
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
    (hp : 1 < p)
    (hmonic : DensePoly.Monic g) :
    DensePoly.Monic (henselLift p k f g h s t).g := by
  sorry

end ZPoly
end Hex
