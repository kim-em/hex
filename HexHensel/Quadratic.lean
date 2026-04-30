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
  QuadraticLiftResult.reduceModSquare (f * g) m

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

private theorem reduceModSquare_congr
    (m : Nat) (f : ZPoly) (hm : 0 < m) :
    ZPoly.congr (QuadraticLiftResult.reduceModSquare f m) f (m * m) := by
  unfold QuadraticLiftResult.reduceModSquare
  have hpow : 0 < m ^ 2 := Nat.pow_pos hm
  simpa [Nat.pow_two] using ZPoly.congr_reduceModPow f m 2 hpow

private theorem addModSquare_congr
    (m : Nat) (f g : ZPoly) (hm : 0 < m) :
    ZPoly.congr (addModSquare f g m) (f + g) (m * m) := by
  unfold addModSquare
  exact reduceModSquare_congr m (f + g) hm

private theorem subModSquare_congr
    (m : Nat) (f g : ZPoly) (hm : 0 < m) :
    ZPoly.congr (subModSquare f g m) (f - g) (m * m) := by
  unfold subModSquare
  exact reduceModSquare_congr m (f - g) hm

private theorem mulModSquare_congr
    (m : Nat) (f g : ZPoly) (hm : 0 < m) :
    ZPoly.congr (mulModSquare f g m) (f * g) (m * m) := by
  unfold mulModSquare
  exact reduceModSquare_congr m (f * g) hm

private theorem congr_sub
    (f g f' g' : ZPoly) (m : Nat)
    (hf : ZPoly.congr f f' m) (hg : ZPoly.congr g g' m) :
    ZPoly.congr (f - g) (f' - g') m := by
  intro i
  rw [DensePoly.coeff_sub f g i]
  · rw [DensePoly.coeff_sub f' g' i]
    · have hfi : (f.coeff i - f'.coeff i) % (m : Int) = 0 := hf i
      have hgi : (g.coeff i - g'.coeff i) % (m : Int) = 0 := hg i
      have hdvd_f : (m : Int) ∣ f.coeff i - f'.coeff i :=
        Int.dvd_of_emod_eq_zero hfi
      have hdvd_g : (m : Int) ∣ g.coeff i - g'.coeff i :=
        Int.dvd_of_emod_eq_zero hgi
      have hcoeff :
          (f.coeff i - g.coeff i) - (f'.coeff i - g'.coeff i) =
            (f.coeff i - f'.coeff i) - (g.coeff i - g'.coeff i) := by
        omega
      rw [hcoeff]
      exact Int.emod_eq_zero_of_dvd (Int.dvd_sub hdvd_f hdvd_g)
    · rfl
  · rfl

private theorem congr_mul_left
    (b x y : ZPoly) (m : Nat)
    (hxy : ZPoly.congr x y m) :
    ZPoly.congr (b * x) (b * y) m :=
  ZPoly.congr_mul b x b y m (ZPoly.congr_refl b m) hxy

private theorem congr_of_square_mod
    (m : Nat) (f g : ZPoly)
    (hfg : ZPoly.congr f g (m * m)) :
    ZPoly.congr f g m := by
  intro i
  by_cases hm : m = 0
  · subst m
    simpa using hfg i
  · have hdiv : (m : Int) ∣ ((m * m : Nat) : Int) := by
      refine ⟨(m : Int), ?_⟩
      rw [Int.natCast_mul]
    have hsqi : (f.coeff i - g.coeff i) % (((m * m : Nat) : Int)) = 0 := hfg i
    exact Int.emod_eq_zero_of_dvd
      (Int.dvd_trans hdiv (Int.dvd_of_emod_eq_zero hsqi))

private theorem sub_self_eq_zero (f : ZPoly) :
    f - f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub, DensePoly.coeff_zero]
  · omega
  · rfl

private theorem coeff_product_right_dvd
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) (i j : Nat) :
    (m : Int) ∣ f.coeff i * g.coeff j := by
  have hj_mod : (g.coeff j) % (m : Int) = 0 := by
    simpa using hg j
  rcases Int.dvd_of_emod_eq_zero hj_mod with ⟨a, ha⟩
  refine ⟨f.coeff i * a, ?_⟩
  calc
    f.coeff i * g.coeff j = f.coeff i * ((m : Int) * a) := by rw [ha]
    _ = (m : Int) * (f.coeff i * a) := by grind

private theorem mulCoeffStep_right_dvd
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) (n i : Nat) (acc : Int) (j : Nat)
    (hacc : (m : Int) ∣ acc) :
    (m : Int) ∣ DensePoly.mulCoeffStep f g n i acc j := by
  by_cases hij : i + j = n
  · rcases hacc with ⟨a, ha⟩
    rcases coeff_product_right_dvd m f g hg i j with ⟨c, hc⟩
    refine ⟨a + c, ?_⟩
    calc
      DensePoly.mulCoeffStep f g n i acc j
          = acc + f.coeff i * g.coeff j := by simp [DensePoly.mulCoeffStep, hij]
      _ = (m : Int) * a + (m : Int) * c := by rw [ha, hc]
      _ = (m : Int) * (a + c) := by grind
  · simpa [DensePoly.mulCoeffStep, hij] using hacc

private theorem foldl_mulCoeffStep_right_dvd
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) (n i : Nat) (xs : List Nat) (acc : Int)
    (hacc : (m : Int) ∣ acc) :
    (m : Int) ∣ xs.foldl (DensePoly.mulCoeffStep f g n i) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons j xs ih =>
      simpa using
        ih (DensePoly.mulCoeffStep f g n i acc j)
          (mulCoeffStep_right_dvd m f g hg n i acc j hacc)

private theorem foldl_mulCoeffSum_right_dvd
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) (n : Nat) (xs : List Nat) (acc : Int)
    (hacc : (m : Int) ∣ acc) :
    (m : Int) ∣
      xs.foldl
        (fun acc i => (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc)
        acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      have hinner :
          (m : Int) ∣
            (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc :=
        foldl_mulCoeffStep_right_dvd m f g hg n i (List.range g.size) acc hacc
      simpa using ih
        ((List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc) hinner

private theorem mul_right_zero_mod_base
    (m : Nat) (f g : ZPoly)
    (hg : ZPoly.congr g 0 m) :
    ZPoly.congr (f * g) 0 m := by
  intro n
  have hdvd : (m : Int) ∣ (f * g).coeff n := by
    rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum]
    exact foldl_mulCoeffSum_right_dvd m f g hg n (List.range f.size) 0 ⟨0, by simp⟩
  rw [DensePoly.coeff_zero]
  simpa using Int.emod_eq_zero_of_dvd hdvd

private theorem divModMonicModSquare_step_reconstruct_congr
    (m : Nat) (quot rem term q : ZPoly) (hm : 0 < m) :
    ZPoly.congr
      (addModSquare quot term m * q + subModSquare rem (mulModSquare term q m) m)
      (quot * q + rem)
      (m * m) := by
  have hquot :
      ZPoly.congr (addModSquare quot term m) (quot + term) (m * m) :=
    addModSquare_congr m quot term hm
  have hrem :
      ZPoly.congr
        (subModSquare rem (mulModSquare term q m) m)
        (rem - mulModSquare term q m)
        (m * m) :=
    subModSquare_congr m rem (mulModSquare term q m) hm
  have hmulMod : ZPoly.congr (mulModSquare term q m) (term * q) (m * m) :=
    mulModSquare_congr m term q hm
  have hrem' :
      ZPoly.congr
        (rem - mulModSquare term q m)
        (rem - term * q)
        (m * m) := by
    intro i
    rw [DensePoly.coeff_sub, DensePoly.coeff_sub]
    · have hcoeff :
          rem.coeff i - (mulModSquare term q m).coeff i -
              (rem.coeff i - (term * q).coeff i) =
            -((mulModSquare term q m).coeff i - (term * q).coeff i) := by
        omega
      rw [hcoeff]
      exact Int.emod_eq_zero_of_dvd
        (Int.dvd_neg.mpr (Int.dvd_of_emod_eq_zero (hmulMod i)))
    · show (0 : Int) - (0 : Int) = 0
      omega
    · show (0 : Int) - (0 : Int) = 0
      omega
  have hleft :
      ZPoly.congr
        (addModSquare quot term m * q + subModSquare rem (mulModSquare term q m) m)
        ((quot + term) * q + (rem - term * q))
        (m * m) :=
    ZPoly.congr_add _ _ _ _ (m * m)
      (ZPoly.congr_mul _ _ _ _ (m * m) hquot (ZPoly.congr_refl q (m * m)))
      (ZPoly.congr_trans _ _ _ (m * m) hrem hrem')
  have hright :
      ZPoly.congr ((quot + term) * q + (rem - term * q)) (quot * q + rem) (m * m) := by
    rw [DensePoly.add_mul_sub_cancel_right]
    exact ZPoly.congr_refl (quot * q + rem) (m * m)
  exact ZPoly.congr_trans _ _ _ (m * m) hleft hright

private theorem divModMonicModSquareAux_reconstruct_congr_of_not_zero
    (m : Nat) (q : ZPoly) (fuel : Nat) (quot rem qOut rOut : ZPoly)
    (hm : 0 < m) (hq : q.isZero = false)
    (hqr : (qOut, rOut) = divModMonicModSquareAux m q fuel quot rem) :
    ZPoly.congr (qOut * q + rOut) (quot * q + rem) (m * m) := by
  induction fuel generalizing quot rem qOut rOut with
  | zero =>
      simp [divModMonicModSquareAux] at hqr
      have hqOut : qOut = quot := hqr.1
      have hrOut : rOut = rem := hqr.2
      subst qOut
      subst rOut
      exact ZPoly.congr_refl (quot * q + rem) (m * m)
  | succ fuel ih =>
      cases hrem : rem.degree? with
      | none =>
          simp [divModMonicModSquareAux, hq, hrem] at hqr
          have hqOut : qOut = quot := hqr.1
          have hrOut : rOut = rem := hqr.2
          subst qOut
          subst rOut
          exact ZPoly.congr_refl (quot * q + rem) (m * m)
      | some rd =>
          cases hqdeg : q.degree? with
          | none =>
              simp [divModMonicModSquareAux, hq, hrem, hqdeg] at hqr
              have hqOut : qOut = quot := hqr.1
              have hrOut : rOut = rem := hqr.2
              subst qOut
              subst rOut
              exact ZPoly.congr_refl (quot * q + rem) (m * m)
          | some qd =>
              by_cases hlt : rd < qd
              · simp [divModMonicModSquareAux, hq, hrem, hqdeg, hlt] at hqr
                have hqOut : qOut = quot := hqr.1
                have hrOut : rOut = rem := hqr.2
                subst qOut
                subst rOut
                exact ZPoly.congr_refl (quot * q + rem) (m * m)
              · simp [divModMonicModSquareAux, hq, hrem, hqdeg, hlt] at hqr
                let k := rd - qd
                let coeff := reduceCoeffModSquare rem.leadingCoeff m
                let term := DensePoly.monomial k coeff
                have hrec :
                    ZPoly.congr (qOut * q + rOut)
                      (addModSquare quot term m * q +
                        subModSquare rem (mulModSquare term q m) m)
                      (m * m) :=
                  ih (addModSquare quot term m)
                    (subModSquare rem (mulModSquare term q m) m)
                    qOut rOut hqr
                have hstep :
                    ZPoly.congr
                      (addModSquare quot term m * q +
                        subModSquare rem (mulModSquare term q m) m)
                      (quot * q + rem)
                      (m * m) :=
                  divModMonicModSquare_step_reconstruct_congr m quot rem term q hm
                exact ZPoly.congr_trans _ _ _ (m * m) hrec hstep

private theorem divModMonicModSquare_reconstruct_congr
    (m : Nat) (p q qOut rOut : ZPoly) (hm : 0 < m)
    (hqr : (qOut, rOut) = divModMonicModSquare p q m) :
    ZPoly.congr (qOut * q + rOut) p (m * m) := by
  unfold divModMonicModSquare at hqr
  let pRed := QuadraticLiftResult.reduceModSquare p m
  change (qOut, rOut) = divModMonicModSquareAux m q pRed.size 0 pRed at hqr
  have hpRed : ZPoly.congr pRed p (m * m) :=
    reduceModSquare_congr m p hm
  cases hq : q.isZero with
  | false =>
    have haux :
        ZPoly.congr (qOut * q + rOut) ((0 : ZPoly) * q + pRed) (m * m) :=
      divModMonicModSquareAux_reconstruct_congr_of_not_zero
        m q pRed.size 0 pRed qOut rOut hm hq hqr
    have hzero :
        ((0 : ZPoly) * q + pRed) = pRed := by
      rw [DensePoly.zero_mul, DensePoly.zero_add]
    exact ZPoly.congr_trans _ _ _ (m * m) haux
      (by
        rw [hzero]
        exact hpRed)
  | true =>
    cases hsize : pRed.size with
    | zero =>
        simp [divModMonicModSquareAux, hsize] at hqr
        have hqOut : qOut = 0 := hqr.1
        have hrOut : rOut = pRed := hqr.2
        subst qOut
        subst rOut
        rw [DensePoly.zero_mul, DensePoly.zero_add]
        exact hpRed
    | succ fuel =>
        simp [divModMonicModSquareAux, hq, hsize] at hqr
        have hqOut : qOut = 0 := hqr.1
        have hrOut : rOut = QuadraticLiftResult.reduceModSquare pRed m := hqr.2
        subst qOut
        subst rOut
        rw [DensePoly.zero_mul, DensePoly.zero_add]
        exact ZPoly.congr_trans _ _ _ (m * m)
          (reduceModSquare_congr m pRed hm) hpRed

private theorem coeff_last_eq_leadingCoeff (f : ZPoly) (hpos : 0 < f.size) :
    f.coeff (f.size - 1) = f.leadingCoeff := by
  cases f with
  | mk coeffs normalized =>
      have hcoeffs : 0 < coeffs.size := by simpa [DensePoly.size] using hpos
      have hidx : coeffs.size - 1 < coeffs.size := Nat.sub_one_lt (Nat.ne_of_gt hcoeffs)
      change coeffs.getD (coeffs.size - 1) 0 = coeffs.back?.getD 0
      rw [Array.back?_eq_getElem?]
      rw [Array.getElem?_eq_getElem hidx]
      exact (Array.getElem_eq_getD 0).symm

private theorem leadingCoeff_zero_mod_base
    (m : Nat) (f : ZPoly) (hf : ZPoly.congr f 0 m) :
    f.leadingCoeff % (m : Int) = 0 := by
  by_cases hpos : 0 < f.size
  · have hcoeff := hf (f.size - 1)
    rw [DensePoly.coeff_zero] at hcoeff
    rw [coeff_last_eq_leadingCoeff f hpos] at hcoeff
    simpa [Int.sub_zero] using hcoeff
  · have hsize : f.size = 0 := Nat.eq_zero_of_not_pos hpos
    have hlead : f.leadingCoeff = 0 := by
      cases f with
      | mk coeffs normalized =>
          simp [DensePoly.leadingCoeff, DensePoly.size] at hsize ⊢
          simp [hsize]
    simp [hlead]

private theorem canonicalMod_congr_self
    (z : Int) (n : Nat) (hn : 0 < n) :
    (canonicalMod z n - z) % (n : Int) = 0 := by
  unfold canonicalMod
  have hnat :
      Int.ofNat (Int.toNat (z % (n : Int))) = z % (n : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)))
  change (Int.ofNat (Int.toNat (z % (n : Int))) - z) % (n : Int) = 0
  rw [hnat]
  exact Int.emod_eq_zero_of_dvd (Int.dvd_sub_self_of_emod_eq rfl)

private theorem reduceCoeffModSquare_zero_mod_base
    (m : Nat) (z : Int)
    (hz : z % (m : Int) = 0) :
    reduceCoeffModSquare z m % (m : Int) = 0 := by
  by_cases hm : m = 0
  · subst m
    simp [reduceCoeffModSquare, canonicalMod] at hz ⊢
    simp [hz]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hsqpos : 0 < m * m := Nat.mul_pos hmpos hmpos
    have hsq :
        (canonicalMod z (m * m) - z) % (((m * m : Nat) : Int)) = 0 :=
      canonicalMod_congr_self z (m * m) hsqpos
    have hz_dvd : (m : Int) ∣ z := Int.dvd_of_emod_eq_zero hz
    have hsq_dvd :
        ((m * m : Nat) : Int) ∣ canonicalMod z (m * m) - z :=
      Int.dvd_of_emod_eq_zero hsq
    have hm_dvd_sq : (m : Int) ∣ ((m * m : Nat) : Int) := by
      refine ⟨(m : Int), ?_⟩
      rw [Int.natCast_mul]
    have hm_dvd_diff : (m : Int) ∣ canonicalMod z (m * m) - z :=
      Int.dvd_trans hm_dvd_sq hsq_dvd
    have hm_dvd_canon : (m : Int) ∣ canonicalMod z (m * m) := by
      rcases hm_dvd_diff with ⟨a, ha⟩
      rcases hz_dvd with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      calc
        canonicalMod z (m * m)
            = (canonicalMod z (m * m) - z) + z := by omega
        _ = (m : Int) * a + (m : Int) * b := by rw [ha, hb]
        _ = (m : Int) * (a + b) := by grind
    simpa [reduceCoeffModSquare, quadraticModulus] using
      Int.emod_eq_zero_of_dvd hm_dvd_canon

private theorem reduceModSquare_zero_mod_base
    (m : Nat) (f : ZPoly)
    (hf : ZPoly.congr f 0 m) :
    ZPoly.congr (QuadraticLiftResult.reduceModSquare f m) 0 m := by
  intro i
  by_cases hm : m = 0
  · subst m
    unfold QuadraticLiftResult.reduceModSquare
    have hfi : f.coeff i = 0 := by simpa using hf i
    rw [ZPoly.coeff_reduceModPow, DensePoly.coeff_zero, hfi]
    rfl
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hsq : ZPoly.congr (QuadraticLiftResult.reduceModSquare f m) f (m * m) :=
      reduceModSquare_congr m f hmpos
    have hsq_i :
        ((QuadraticLiftResult.reduceModSquare f m).coeff i - f.coeff i) %
            (((m * m : Nat) : Int)) = 0 :=
      hsq i
    have hdiff_dvd :
        ((m * m : Nat) : Int) ∣
          (QuadraticLiftResult.reduceModSquare f m).coeff i - f.coeff i :=
      Int.dvd_of_emod_eq_zero hsq_i
    have hm_dvd_sq : (m : Int) ∣ ((m * m : Nat) : Int) := by
      refine ⟨(m : Int), ?_⟩
      rw [Int.natCast_mul]
    have hm_dvd_diff :
        (m : Int) ∣ (QuadraticLiftResult.reduceModSquare f m).coeff i - f.coeff i :=
      Int.dvd_trans hm_dvd_sq hdiff_dvd
    have hf_i : (m : Int) ∣ f.coeff i := by
      exact Int.dvd_of_emod_eq_zero (by simpa using hf i)
    have hred_dvd : (m : Int) ∣ (QuadraticLiftResult.reduceModSquare f m).coeff i := by
      rcases hm_dvd_diff with ⟨a, ha⟩
      rcases hf_i with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      calc
        (QuadraticLiftResult.reduceModSquare f m).coeff i
            =
              ((QuadraticLiftResult.reduceModSquare f m).coeff i - f.coeff i) +
                f.coeff i := by omega
        _ = (m : Int) * a + (m : Int) * b := by rw [ha, hb]
        _ = (m : Int) * (a + b) := by grind
    rw [DensePoly.coeff_zero]
    simpa using Int.emod_eq_zero_of_dvd hred_dvd

private theorem addModSquare_zero_mod_base
    (m : Nat) (f g : ZPoly)
    (hf : ZPoly.congr f 0 m) (hg : ZPoly.congr g 0 m) :
    ZPoly.congr (addModSquare f g m) 0 m := by
  unfold addModSquare
  apply reduceModSquare_zero_mod_base
  intro i
  rw [DensePoly.coeff_add]
  · have hfi : (f.coeff i) % (m : Int) = 0 := by simpa using hf i
    have hgi : (g.coeff i) % (m : Int) = 0 := by simpa using hg i
    simpa [Int.sub_zero] using
      Int.emod_eq_zero_of_dvd (Int.dvd_add
        (Int.dvd_of_emod_eq_zero hfi) (Int.dvd_of_emod_eq_zero hgi))
  · rfl

private theorem subModSquare_zero_mod_base
    (m : Nat) (f g : ZPoly)
    (hf : ZPoly.congr f 0 m) (hg : ZPoly.congr g 0 m) :
    ZPoly.congr (subModSquare f g m) 0 m := by
  unfold subModSquare
  apply reduceModSquare_zero_mod_base
  intro i
  rw [DensePoly.coeff_sub]
  · have hfi : (f.coeff i) % (m : Int) = 0 := by simpa using hf i
    have hgi : (g.coeff i) % (m : Int) = 0 := by simpa using hg i
    simpa [Int.sub_zero] using
      Int.emod_eq_zero_of_dvd (Int.dvd_sub
        (Int.dvd_of_emod_eq_zero hfi) (Int.dvd_of_emod_eq_zero hgi))
  · rfl

private theorem mulModSquare_left_zero_mod_base
    (m : Nat) (f g : ZPoly)
    (hf : ZPoly.congr f 0 m) :
    ZPoly.congr (mulModSquare f g m) 0 m := by
  unfold mulModSquare
  apply reduceModSquare_zero_mod_base
  simpa [DensePoly.zero_mul] using
    ZPoly.congr_mul f g 0 g m hf (ZPoly.congr_refl g m)

private theorem monomial_zero_mod_base
    (m k : Nat) (c : Int)
    (hc : c % (m : Int) = 0) :
    ZPoly.congr (DensePoly.monomial k c) 0 m := by
  intro i
  rw [DensePoly.coeff_monomial, DensePoly.coeff_zero]
  by_cases hi : i = k
  · simp [hi, hc]
  · rw [if_neg hi]
    change ((0 : Int) - 0) % (m : Int) = 0
    simp

private theorem divModMonicModSquareAux_zero_mod_base
    (m : Nat) (q : ZPoly) (fuel : Nat) (quot rem qOut rOut : ZPoly)
    (hquot : ZPoly.congr quot 0 m)
    (hrem : ZPoly.congr rem 0 m)
    (hqr : (qOut, rOut) = divModMonicModSquareAux m q fuel quot rem) :
    ZPoly.congr qOut 0 m ∧ ZPoly.congr rOut 0 m := by
  induction fuel generalizing quot rem qOut rOut with
  | zero =>
      simp [divModMonicModSquareAux] at hqr
      rcases hqr with ⟨hqOut, hrOut⟩
      rw [hqOut, hrOut]
      exact ⟨hquot, hrem⟩
  | succ fuel ih =>
      cases hq : q.isZero with
      | true =>
          simp [divModMonicModSquareAux, hq] at hqr
          rcases hqr with ⟨hqOut, hrOut⟩
          rw [hqOut, hrOut]
          exact ⟨ZPoly.congr_refl 0 m, reduceModSquare_zero_mod_base m rem hrem⟩
      | false =>
          cases hremDeg : rem.degree? with
          | none =>
              simp [divModMonicModSquareAux, hq, hremDeg] at hqr
              rcases hqr with ⟨hqOut, hrOut⟩
              rw [hqOut, hrOut]
              exact ⟨hquot, hrem⟩
          | some rd =>
              cases hqdeg : q.degree? with
              | none =>
                  simp [divModMonicModSquareAux, hq, hremDeg, hqdeg] at hqr
                  rcases hqr with ⟨hqOut, hrOut⟩
                  rw [hqOut, hrOut]
                  exact ⟨hquot, hrem⟩
              | some qd =>
                  by_cases hlt : rd < qd
                  · simp [divModMonicModSquareAux, hq, hremDeg, hqdeg, hlt] at hqr
                    rcases hqr with ⟨hqOut, hrOut⟩
                    rw [hqOut, hrOut]
                    exact ⟨hquot, hrem⟩
                  · simp [divModMonicModSquareAux, hq, hremDeg, hqdeg, hlt] at hqr
                    let k := rd - qd
                    let coeff := reduceCoeffModSquare rem.leadingCoeff m
                    let term := DensePoly.monomial k coeff
                    have hcoeff : coeff % (m : Int) = 0 := by
                      exact reduceCoeffModSquare_zero_mod_base m rem.leadingCoeff
                        (leadingCoeff_zero_mod_base m rem hrem)
                    have hterm : ZPoly.congr term 0 m :=
                      monomial_zero_mod_base m k coeff hcoeff
                    have hquot' : ZPoly.congr (addModSquare quot term m) 0 m :=
                      addModSquare_zero_mod_base m quot term hquot hterm
                    have hmul : ZPoly.congr (mulModSquare term q m) 0 m :=
                      mulModSquare_left_zero_mod_base m term q hterm
                    have hrem' :
                        ZPoly.congr (subModSquare rem (mulModSquare term q m) m) 0 m :=
                      subModSquare_zero_mod_base m rem (mulModSquare term q m) hrem hmul
                    exact ih (addModSquare quot term m)
                      (subModSquare rem (mulModSquare term q m) m)
                      qOut rOut hquot' hrem' hqr

private theorem divModMonicModSquare_zero_mod_base
    (m : Nat) (p q qOut rOut : ZPoly)
    (hp : ZPoly.congr p 0 m)
    (hqr : (qOut, rOut) = divModMonicModSquare p q m) :
    ZPoly.congr qOut 0 m ∧ ZPoly.congr rOut 0 m := by
  unfold divModMonicModSquare at hqr
  let pRed := QuadraticLiftResult.reduceModSquare p m
  change (qOut, rOut) = divModMonicModSquareAux m q pRed.size 0 pRed at hqr
  exact divModMonicModSquareAux_zero_mod_base m q pRed.size 0 pRed qOut rOut
    (ZPoly.congr_refl 0 m)
    (reduceModSquare_zero_mod_base m p hp)
    hqr

private theorem quadraticHenselStep_bezout_error_definition_congr
    (m : Nat) (s t g' h' b : ZPoly) (hm : 0 < m)
    (hb :
      b =
        subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m) :
    ZPoly.congr b (s * g' + t * h' - 1) (m * m) := by
  rw [hb]
  have hsg : ZPoly.congr (mulModSquare s g' m) (s * g') (m * m) :=
    mulModSquare_congr m s g' hm
  have hth : ZPoly.congr (mulModSquare t h' m) (t * h') (m * m) :=
    mulModSquare_congr m t h' hm
  have hadd₀ :
      ZPoly.congr
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
        (mulModSquare s g' m + mulModSquare t h' m)
        (m * m) :=
    addModSquare_congr m (mulModSquare s g' m) (mulModSquare t h' m) hm
  have hadd₁ :
      ZPoly.congr
        (mulModSquare s g' m + mulModSquare t h' m)
        (s * g' + t * h')
        (m * m) :=
    ZPoly.congr_add (mulModSquare s g' m) (mulModSquare t h' m) (s * g') (t * h')
      (m * m) hsg hth
  have hadd :
      ZPoly.congr
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
        (s * g' + t * h')
        (m * m) :=
    ZPoly.congr_trans _ _ _ (m * m) hadd₀ hadd₁
  have hsub₀ :
      ZPoly.congr
        (subModSquare (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m)
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
        (m * m) :=
    subModSquare_congr m
      (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 hm
  have hsub₁ :
      ZPoly.congr
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
        (s * g' + t * h' - 1)
        (m * m) :=
    by
      intro i
      rw [DensePoly.coeff_sub, DensePoly.coeff_sub]
      · have hcoeff :
            DensePoly.coeff
                (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) i -
                DensePoly.coeff (s * g' + t * h') i =
              DensePoly.coeff
                  (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) i -
                  DensePoly.coeff (1 : ZPoly) i -
                (DensePoly.coeff (s * g' + t * h') i -
                  DensePoly.coeff (1 : ZPoly) i) := by
          omega
        rw [← hcoeff]
        exact hadd i
      · show (0 : Int) - (0 : Int) = 0
        omega
      · show (0 : Int) - (0 : Int) = 0
        omega
  exact
    ZPoly.congr_trans
      (subModSquare
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m)
      (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
      (s * g' + t * h' - 1)
      (m * m)
      hsub₀
      hsub₁

private theorem quadraticHenselStep_bezout_correction_exact
    (g h s t b q r : ZPoly) :
    ((s - s * b - q * h) * g + (t - r) * h) =
      (s * g + t * h) - (s * b * g + (q * g + r) * h) := by
  calc
    ((s - s * b - q * h) * g + (t - r) * h)
        = ((s - s * b) * g + (0 - q * h) * g) + (t - r) * h := by
          rw [DensePoly.sub_eq_add_neg_poly (s - s * b) (q * h)]
          rw [DensePoly.mul_add_left_poly]
    _ = ((s * g + (0 - s * b) * g) + (0 - q * h) * g) + (t - r) * h := by
          rw [DensePoly.sub_eq_add_neg_poly s (s * b)]
          rw [DensePoly.mul_add_left_poly]
    _ = ((s * g + (0 - s * b * g)) + (0 - (q * h) * g)) + (t - r) * h := by
          rw [DensePoly.neg_mul_right_poly (s * b) g]
          rw [DensePoly.neg_mul_right_poly (q * h) g]
    _ = ((s * g + (0 - s * b * g)) + (0 - (q * g) * h)) + (t - r) * h := by
          rw [DensePoly.mul_assoc_poly q h g]
          rw [DensePoly.mul_comm_poly h g]
          rw [← DensePoly.mul_assoc_poly q g h]
    _ = ((s * g + (0 - s * b * g)) + (0 - (q * g) * h)) +
          (t * h + (0 - r) * h) := by
          rw [DensePoly.sub_eq_add_neg_poly t r]
          rw [DensePoly.mul_add_left_poly]
    _ = ((s * g + (0 - s * b * g)) + (0 - (q * g) * h)) +
          (t * h + (0 - r * h)) := by
          rw [DensePoly.neg_mul_right_poly r h]
    _ = (s * g + t * h) + (0 - (s * b * g + ((q * g) * h + r * h))) := by
          apply DensePoly.ext_coeff
          intro n
          repeat
            first
            | rw [DensePoly.coeff_add]
            | rw [DensePoly.coeff_sub]
            | rw [DensePoly.coeff_zero]
          all_goals try rfl
          omega
    _ = (s * g + t * h) + (0 - (s * b * g + (q * g + r) * h)) := by
          rw [DensePoly.mul_add_left_poly]
    _ = (s * g + t * h) - (s * b * g + (q * g + r) * h) := by
          exact (DensePoly.sub_eq_add_neg_poly
            (s * g + t * h) (s * b * g + (q * g + r) * h)).symm

private theorem quadraticHenselStep_bezout_mul_error_exact
    (g h s t b : ZPoly) :
    s * b * g + (t * b) * h = b * (s * g + t * h) := by
  calc
    s * b * g + (t * b) * h
        = b * s * g + (t * b) * h := by
          rw [DensePoly.mul_comm_poly s b]
    _ = b * s * g + b * t * h := by
          rw [DensePoly.mul_comm_poly t b]
    _ = b * (s * g) + b * t * h := by
          rw [DensePoly.mul_assoc_poly b s g]
    _ = b * (s * g) + b * (t * h) := by
          rw [DensePoly.mul_assoc_poly b t h]
    _ = b * (s * g + t * h) := by
          rw [← DensePoly.mul_add_right_poly b (s * g) (t * h)]

private theorem quadraticHenselStep_sub_one_add_one_exact
    (x : ZPoly) :
    (x - 1) + 1 = x := by
  apply DensePoly.ext_coeff
  intro n
  repeat
    first
    | rw [DensePoly.coeff_add]
    | rw [DensePoly.coeff_sub]
    | rw [DensePoly.coeff_zero]
  all_goals try rfl
  omega

private theorem quadraticHenselStep_one_sub_error_exact
    (b : ZPoly) :
    (b + 1) - b * (b + 1) = 1 - b * b := by
  calc
    (b + 1) - b * (b + 1)
        = (b + 1) - (b * b + b * 1) := by
          rw [DensePoly.mul_add_right_poly]
    _ = (b + 1) - (b * b + b) := by
          rw [DensePoly.mul_one_right_poly]
    _ = 1 + (0 - b * b) := by
          rw [DensePoly.add_sub_add_swap b 1 (b * b)]
    _ = 1 - b * b := by
          exact (DensePoly.sub_eq_add_neg_poly 1 (b * b)).symm

private theorem quadraticHenselStep_bezout_correction_algebra
    (m : Nat)
    (g' h' s t b qBezout rBezout : ZPoly)
    (hm : 0 < m)
    (hb : ZPoly.congr b (s * g' + t * h' - 1) (m * m))
    (hdiv : ZPoly.congr (qBezout * g' + rBezout) (t * b) (m * m)) :
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') (1 - b * b) (m * m) := by
  intro t' s'
  have hsb :
      ZPoly.congr (mulModSquare s b m) (s * b) (m * m) :=
    mulModSquare_congr m s b hm
  have hsMinus :
      ZPoly.congr
        (subModSquare s (mulModSquare s b m) m)
        (s - s * b)
        (m * m) := by
    have hred :
        ZPoly.congr
          (subModSquare s (mulModSquare s b m) m)
          (s - mulModSquare s b m)
          (m * m) :=
      subModSquare_congr m s (mulModSquare s b m) hm
    have hplain :
        ZPoly.congr (s - mulModSquare s b m) (s - s * b) (m * m) :=
      congr_sub s (mulModSquare s b m) s (s * b) (m * m)
        (ZPoly.congr_refl s (m * m)) hsb
    exact ZPoly.congr_trans _ _ _ (m * m) hred hplain
  have hqh :
      ZPoly.congr (mulModSquare qBezout h' m) (qBezout * h') (m * m) :=
    mulModSquare_congr m qBezout h' hm
  have hs' :
      ZPoly.congr s' (s - s * b - qBezout * h') (m * m) := by
    have hred :
        ZPoly.congr
          (subModSquare
            (subModSquare s (mulModSquare s b m) m)
            (mulModSquare qBezout h' m) m)
          (subModSquare s (mulModSquare s b m) m - mulModSquare qBezout h' m)
          (m * m) :=
      subModSquare_congr m
        (subModSquare s (mulModSquare s b m) m)
        (mulModSquare qBezout h' m) hm
    have hplain :
        ZPoly.congr
          (subModSquare s (mulModSquare s b m) m - mulModSquare qBezout h' m)
          (s - s * b - qBezout * h')
          (m * m) :=
      congr_sub
        (subModSquare s (mulModSquare s b m) m)
        (mulModSquare qBezout h' m)
        (s - s * b)
        (qBezout * h')
        (m * m)
        hsMinus
        hqh
    exact ZPoly.congr_trans s'
      (subModSquare s (mulModSquare s b m) m - mulModSquare qBezout h' m)
      (s - s * b - qBezout * h')
      (m * m)
      (by simpa [s'] using hred)
      hplain
  have ht' : ZPoly.congr t' (t - rBezout) (m * m) :=
    by simpa [t'] using subModSquare_congr m t rBezout hm
  have hleft :
      ZPoly.congr
        (s' * g' + t' * h')
        ((s - s * b - qBezout * h') * g' + (t - rBezout) * h')
        (m * m) :=
    ZPoly.congr_add (s' * g') (t' * h')
      ((s - s * b - qBezout * h') * g') ((t - rBezout) * h')
      (m * m)
      (ZPoly.congr_mul s' g' (s - s * b - qBezout * h') g'
        (m * m) hs' (ZPoly.congr_refl g' (m * m)))
      (ZPoly.congr_mul t' h' (t - rBezout) h'
        (m * m) ht' (ZPoly.congr_refl h' (m * m)))
  let a := s * g' + t * h'
  have hnormalized :
      ((s - s * b - qBezout * h') * g' + (t - rBezout) * h') =
        a - (s * b * g' + (qBezout * g' + rBezout) * h') := by
    simpa [a] using
      quadraticHenselStep_bezout_correction_exact
        g' h' s t b qBezout rBezout
  have hdivH :
      ZPoly.congr
        ((qBezout * g' + rBezout) * h')
        ((t * b) * h')
        (m * m) :=
    ZPoly.congr_mul (qBezout * g' + rBezout) h' (t * b) h'
      (m * m) hdiv (ZPoly.congr_refl h' (m * m))
  have hsecond :
      ZPoly.congr
        (s * b * g' + (qBezout * g' + rBezout) * h')
        (b * a)
        (m * m) := by
    have hsum :
        ZPoly.congr
          (s * b * g' + (qBezout * g' + rBezout) * h')
          (s * b * g' + (t * b) * h')
          (m * m) :=
      ZPoly.congr_add (s * b * g') ((qBezout * g' + rBezout) * h')
        (s * b * g') ((t * b) * h')
        (m * m)
        (ZPoly.congr_refl (s * b * g') (m * m))
        hdivH
    have hexact :
        s * b * g' + (t * b) * h' = b * a := by
      simpa [a] using quadraticHenselStep_bezout_mul_error_exact g' h' s t b
    exact ZPoly.congr_trans _ _ _ (m * m) hsum
      (by simpa [hexact] using ZPoly.congr_refl (s * b * g' + (t * b) * h') (m * m))
  have ha : ZPoly.congr a (b + 1) (m * m) := by
    have hadd :
        ZPoly.congr (b + 1) ((a - 1) + 1) (m * m) :=
      ZPoly.congr_add b 1 (a - 1) 1 (m * m) hb (ZPoly.congr_refl 1 (m * m))
    exact ZPoly.congr_symm _ _ _ <|
      ZPoly.congr_trans (b + 1) ((a - 1) + 1) a (m * m) hadd
        (by
          simpa [quadraticHenselStep_sub_one_add_one_exact a] using
            ZPoly.congr_refl ((a - 1) + 1) (m * m))
  have hright :
      ZPoly.congr
        (a - (s * b * g' + (qBezout * g' + rBezout) * h'))
        ((b + 1) - b * (b + 1))
        (m * m) := by
    exact congr_sub a (s * b * g' + (qBezout * g' + rBezout) * h')
      (b + 1) (b * (b + 1)) (m * m)
      ha
      (ZPoly.congr_trans _ _ _ (m * m) hsecond
        (congr_mul_left b a (b + 1) (m * m) ha))
  exact ZPoly.congr_trans
    (s' * g' + t' * h')
    (a - (s * b * g' + (qBezout * g' + rBezout) * h'))
    (1 - b * b)
    (m * m)
    (ZPoly.congr_trans _ _ _ (m * m) hleft
      (by
        simpa [hnormalized] using
          ZPoly.congr_refl
            ((s - s * b - qBezout * h') * g' + (t - rBezout) * h')
            (m * m)))
    (ZPoly.congr_trans _ _ _ (m * m) hright
      (by
        simpa [quadraticHenselStep_one_sub_error_exact b] using
          ZPoly.congr_refl ((b + 1) - b * (b + 1)) (m * m)))

private theorem quadraticHenselStep_bezout_error_from_factor_update
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (_hmonic : DensePoly.Monic g) :
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
  intro e te factorQR qFactor rFactor g' hCorrection h' b
  have hm0 : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
  have he : ZPoly.congr e 0 m := by
    have hf : ZPoly.congr f (g * h) m := ZPoly.congr_symm (g * h) f m hprod
    simpa [e, QuadraticLiftResult.factorError, sub_self_eq_zero (g * h)] using
      congr_sub f (g * h) (g * h) (g * h) m hf (ZPoly.congr_refl (g * h) m)
  have hte : ZPoly.congr te 0 m := by
    have hmul : ZPoly.congr (mulModSquare t e m) (t * e) (m * m) :=
      mulModSquare_congr m t e hm0
    have hmulBase : ZPoly.congr (t * e) 0 m := by
      exact mul_right_zero_mod_base m t e he
    exact ZPoly.congr_trans te (t * e) 0 m
      (congr_of_square_mod m te (t * e) (by simpa [te] using hmul)) hmulBase
  have hpair : (qFactor, rFactor) = divModMonicModSquare te g m := by
    simp [factorQR, qFactor, rFactor]
  have hqr : ZPoly.congr qFactor 0 m ∧ ZPoly.congr rFactor 0 m :=
    divModMonicModSquare_zero_mod_base m te g qFactor rFactor hte hpair
  have hg' : ZPoly.congr g' g m := by
    have hadd : ZPoly.congr (addModSquare g rFactor m) (g + rFactor) (m * m) :=
      addModSquare_congr m g rFactor hm0
    have hbase : ZPoly.congr (g + rFactor) (g + 0) m :=
      ZPoly.congr_add g rFactor g 0 m (ZPoly.congr_refl g m) hqr.2
    have hzero : (g + (0 : ZPoly)) = g := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_add, DensePoly.coeff_zero]
      · omega
      · rfl
    exact ZPoly.congr_trans g' (g + rFactor) g m
      (congr_of_square_mod m g' (g + rFactor) (by simpa [g'] using hadd))
      (by simpa [hzero] using hbase)
  have hCorrection_zero : ZPoly.congr hCorrection 0 m := by
    have hseSq : ZPoly.congr (mulModSquare s e m) (s * e) (m * m) :=
      mulModSquare_congr m s e hm0
    have hse : ZPoly.congr (mulModSquare s e m) 0 m := by
      have hmulBase : ZPoly.congr (s * e) 0 m := by
        exact mul_right_zero_mod_base m s e he
      exact ZPoly.congr_trans (mulModSquare s e m) (s * e) 0 m
        (congr_of_square_mod m (mulModSquare s e m) (s * e) hseSq) hmulBase
    have hqhSq : ZPoly.congr (mulModSquare qFactor h m) (qFactor * h) (m * m) :=
      mulModSquare_congr m qFactor h hm0
    have hqh : ZPoly.congr (mulModSquare qFactor h m) 0 m := by
      have hmulBase : ZPoly.congr (qFactor * h) 0 m := by
        simpa [DensePoly.zero_mul] using
          ZPoly.congr_mul qFactor h 0 h m hqr.1 (ZPoly.congr_refl h m)
      exact ZPoly.congr_trans (mulModSquare qFactor h m) (qFactor * h) 0 m
        (congr_of_square_mod m (mulModSquare qFactor h m) (qFactor * h) hqhSq) hmulBase
    have hadd :
        ZPoly.congr
          (addModSquare (mulModSquare s e m) (mulModSquare qFactor h m) m)
          (mulModSquare s e m + mulModSquare qFactor h m)
          (m * m) :=
      addModSquare_congr m (mulModSquare s e m) (mulModSquare qFactor h m) hm0
    have hsum : ZPoly.congr (mulModSquare s e m + mulModSquare qFactor h m) 0 m := by
      simpa [DensePoly.zero_add] using
        ZPoly.congr_add (mulModSquare s e m) (mulModSquare qFactor h m) 0 0 m hse hqh
    exact ZPoly.congr_trans hCorrection
      (mulModSquare s e m + mulModSquare qFactor h m) 0 m
      (congr_of_square_mod m hCorrection
        (mulModSquare s e m + mulModSquare qFactor h m)
        (by simpa [hCorrection] using hadd))
      hsum
  have hh' : ZPoly.congr h' h m := by
    have hadd : ZPoly.congr (addModSquare h hCorrection m) (h + hCorrection) (m * m) :=
      addModSquare_congr m h hCorrection hm0
    have hbase : ZPoly.congr (h + hCorrection) (h + 0) m :=
      ZPoly.congr_add h hCorrection h 0 m (ZPoly.congr_refl h m) hCorrection_zero
    have hzero : (h + (0 : ZPoly)) = h := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_add, DensePoly.coeff_zero]
      · omega
      · rfl
    exact ZPoly.congr_trans h' (h + hCorrection) h m
      (congr_of_square_mod m h' (h + hCorrection) (by simpa [h'] using hadd))
      (by simpa [hzero] using hbase)
  have hsg : ZPoly.congr (mulModSquare s g' m) (s * g) m := by
    have hsq : ZPoly.congr (mulModSquare s g' m) (s * g') (m * m) :=
      mulModSquare_congr m s g' hm0
    exact ZPoly.congr_trans (mulModSquare s g' m) (s * g') (s * g) m
      (congr_of_square_mod m (mulModSquare s g' m) (s * g') hsq)
      (ZPoly.congr_mul s g' s g m (ZPoly.congr_refl s m) hg')
  have hth : ZPoly.congr (mulModSquare t h' m) (t * h) m := by
    have hsq : ZPoly.congr (mulModSquare t h' m) (t * h') (m * m) :=
      mulModSquare_congr m t h' hm0
    exact ZPoly.congr_trans (mulModSquare t h' m) (t * h') (t * h) m
      (congr_of_square_mod m (mulModSquare t h' m) (t * h') hsq)
      (ZPoly.congr_mul t h' t h m (ZPoly.congr_refl t m) hh')
  have haddInner :
      ZPoly.congr
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
        (s * g + t * h)
        m := by
    have haddSq :
        ZPoly.congr
          (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
          (mulModSquare s g' m + mulModSquare t h' m)
          (m * m) :=
      addModSquare_congr m (mulModSquare s g' m) (mulModSquare t h' m) hm0
    have haddBase :
        ZPoly.congr
          (mulModSquare s g' m + mulModSquare t h' m)
          (s * g + t * h)
          m :=
      ZPoly.congr_add (mulModSquare s g' m) (mulModSquare t h' m)
        (s * g) (t * h) m hsg hth
    exact ZPoly.congr_trans
      (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
      (mulModSquare s g' m + mulModSquare t h' m)
      (s * g + t * h) m
      (congr_of_square_mod m
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m)
        (mulModSquare s g' m + mulModSquare t h' m)
        haddSq)
      haddBase
  have hbToError :
      ZPoly.congr b (s * g + t * h - 1) m := by
    have hsubSq :
        ZPoly.congr
          (subModSquare
            (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 m)
          (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
          (m * m) :=
      subModSquare_congr m
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1 hm0
    exact ZPoly.congr_trans b
      (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
      (s * g + t * h - 1)
      m
      (congr_of_square_mod m b
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m - 1)
        (by simpa [b] using hsubSq))
      (congr_sub
        (addModSquare (mulModSquare s g' m) (mulModSquare t h' m) m) 1
        (s * g + t * h) 1 m haddInner (ZPoly.congr_refl 1 m))
  have htarget : ZPoly.congr (s * g + t * h - 1) 0 m := by
    simpa using congr_sub (s * g + t * h) 1 1 1 m hbez (ZPoly.congr_refl 1 m)
  exact ZPoly.congr_trans b (s * g + t * h - 1) 0 m hbToError htarget

private theorem quadraticHenselStep_bezout_correction_congr_core
    (m : Nat)
    (g' h' s t b qBezout rBezout : ZPoly)
    (hm : 1 < m)
    (hb : ZPoly.congr b (s * g' + t * h' - 1) (m * m))
    (hbezoutQR :
      let tb := mulModSquare t b m
      let bezoutQR := divModMonicModSquare tb g' m
      qBezout = bezoutQR.1 ∧ rBezout = bezoutQR.2) :
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') (1 - b * b) (m * m) := by
  have hm0 : 0 < m := Nat.lt_trans Nat.zero_lt_one hm
  let tb := mulModSquare t b m
  let bezoutQR := divModMonicModSquare tb g' m
  have hpair : (qBezout, rBezout) = bezoutQR := by
    rcases hbezoutQR with ⟨hq, hr⟩
    exact Prod.ext hq hr
  have hdivMod :
      ZPoly.congr (qBezout * g' + rBezout) tb (m * m) :=
    divModMonicModSquare_reconstruct_congr m tb g' qBezout rBezout hm0 hpair
  have hmul : ZPoly.congr tb (t * b) (m * m) :=
    mulModSquare_congr m t b hm0
  have hdiv : ZPoly.congr (qBezout * g' + rBezout) (t * b) (m * m) :=
    ZPoly.congr_trans (qBezout * g' + rBezout) tb (t * b) (m * m) hdivMod hmul
  simpa [tb] using
    quadraticHenselStep_bezout_correction_algebra
      m g' h' s t b qBezout rBezout hm0 hb hdiv

private theorem coeff_product_dvd_mod_square
    (m : Nat) (b : ZPoly)
    (hb : ZPoly.congr b 0 m) (i j : Nat) :
    ((m * m : Nat) : Int) ∣ b.coeff i * b.coeff j := by
  have hi_mod : (b.coeff i) % (m : Int) = 0 := by
    simpa using hb i
  have hj_mod : (b.coeff j) % (m : Int) = 0 := by
    simpa using hb j
  rcases Int.dvd_of_emod_eq_zero hi_mod with ⟨ai, hai⟩
  rcases Int.dvd_of_emod_eq_zero hj_mod with ⟨aj, haj⟩
  refine ⟨ai * aj, ?_⟩
  calc
    b.coeff i * b.coeff j
        = ((m : Int) * ai) * ((m : Int) * aj) := by rw [← hai, ← haj]
    _ = ((m * m : Nat) : Int) * (ai * aj) := by
          grind

private theorem mulCoeffStep_dvd_mod_square
    (m : Nat) (b : ZPoly)
    (hb : ZPoly.congr b 0 m) (n i : Nat) (acc : Int) (j : Nat)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣ DensePoly.mulCoeffStep b b n i acc j := by
  by_cases hij : i + j = n
  · rcases hacc with ⟨a, ha⟩
    rcases coeff_product_dvd_mod_square m b hb i j with ⟨c, hc⟩
    refine ⟨a + c, ?_⟩
    calc
      DensePoly.mulCoeffStep b b n i acc j
          = acc + b.coeff i * b.coeff j := by simp [DensePoly.mulCoeffStep, hij]
      _ = ((m * m : Nat) : Int) * a + ((m * m : Nat) : Int) * c := by rw [ha, hc]
      _ = ((m * m : Nat) : Int) * (a + c) := by grind
  · simpa [DensePoly.mulCoeffStep, hij] using hacc

private theorem foldl_mulCoeffStep_dvd_mod_square
    (m : Nat) (b : ZPoly)
    (hb : ZPoly.congr b 0 m) (n i : Nat) (xs : List Nat) (acc : Int)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣
      xs.foldl (DensePoly.mulCoeffStep b b n i) acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons j xs ih =>
      simpa using
        ih (DensePoly.mulCoeffStep b b n i acc j)
          (mulCoeffStep_dvd_mod_square m b hb n i acc j hacc)

private theorem foldl_mulCoeffSum_dvd_mod_square
    (m : Nat) (b : ZPoly)
    (hb : ZPoly.congr b 0 m) (n : Nat) (xs : List Nat) (acc : Int)
    (hacc : ((m * m : Nat) : Int) ∣ acc) :
    ((m * m : Nat) : Int) ∣
      xs.foldl
        (fun acc i => (List.range b.size).foldl (DensePoly.mulCoeffStep b b n i) acc)
        acc := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      have hinner :
          ((m * m : Nat) : Int) ∣
            (List.range b.size).foldl (DensePoly.mulCoeffStep b b n i) acc :=
        foldl_mulCoeffStep_dvd_mod_square m b hb n i (List.range b.size) acc hacc
      simpa using ih
        ((List.range b.size).foldl (DensePoly.mulCoeffStep b b n i) acc) hinner

private theorem square_congr_zero_mod_square
    (m : Nat) (b : ZPoly)
    (_hm : 1 < m)
    (hb : ZPoly.congr b 0 m) :
    ZPoly.congr (b * b) 0 (m * m) := by
  intro n
  have hdvd :
      ((m * m : Nat) : Int) ∣ (b * b).coeff n := by
    rw [DensePoly.coeff_mul, DensePoly.mulCoeffSum]
    exact foldl_mulCoeffSum_dvd_mod_square m b hb n (List.range b.size) 0 ⟨0, by simp⟩
  simpa using Int.emod_eq_zero_of_dvd hdvd

private theorem one_sub_square_congr_one_of_square_congr_zero
    (m : Nat) (b : ZPoly)
    (_hm : 1 < m)
    (hb2 : ZPoly.congr (b * b) 0 (m * m)) :
    ZPoly.congr (1 - b * b) 1 (m * m) := by
  intro i
  have hb2i : ((b * b).coeff i) % ((m * m : Nat) : Int) = 0 := by
    simpa using hb2 i
  have hdvd : ((m * m : Nat) : Int) ∣ (b * b).coeff i :=
    Int.dvd_of_emod_eq_zero hb2i
  have hneg : ((m * m : Nat) : Int) ∣ -((b * b).coeff i) :=
    Int.dvd_neg.mpr hdvd
  have hcoeff :
      ((1 - b * b : ZPoly).coeff i - (1 : ZPoly).coeff i) =
        -((b * b).coeff i) := by
    rw [DensePoly.coeff_sub]
    · omega
    · rfl
  rw [hcoeff]
  exact Int.emod_eq_zero_of_dvd hneg

private theorem quadraticHenselStep_bezout_error_congr_zero_core
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
  exact quadraticHenselStep_bezout_error_from_factor_update m f g h s t hm hprod hbez hmonic

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
  exact quadraticHenselStep_bezout_error_congr_zero_core m f g h s t hm hprod hbez hmonic

private theorem quadraticHenselStep_bezout_correction_congr
    (m : Nat)
    (f g h s t : ZPoly)
    (hm : 1 < m)
    (_hprod : ZPoly.congr (g * h) f m)
    (_hbez : ZPoly.congr (s * g + t * h) 1 m)
    (_hmonic : DensePoly.Monic g) :
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
  intro e te factorQR qFactor rFactor g' hCorrection h' b tb bezoutQR qBezout rBezout t' s'
  have hbezoutQR :
      (let tb := mulModSquare t b m
       let bezoutQR := divModMonicModSquare tb g' m
       qBezout = bezoutQR.1 ∧ rBezout = bezoutQR.2) := by
    simp [tb, bezoutQR, qBezout, rBezout]
  have hb :
      ZPoly.congr b (s * g' + t * h' - 1) (m * m) :=
    quadraticHenselStep_bezout_error_definition_congr m s t g' h' b
      (Nat.lt_trans Nat.zero_lt_one hm)
      (by simp [b])
  simpa [t', s'] using
    quadraticHenselStep_bezout_correction_congr_core
      m g' h' s t b qBezout rBezout hm hb hbezoutQR

private theorem congr_one_sub_square_of_congr_zero
    (m : Nat) (b : ZPoly)
    (hm : 1 < m)
    (hb : ZPoly.congr b 0 m) :
    ZPoly.congr (1 - b * b) 1 (m * m) := by
  exact one_sub_square_congr_one_of_square_congr_zero m b hm
    (square_congr_zero_mod_square m b hm hb)

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
