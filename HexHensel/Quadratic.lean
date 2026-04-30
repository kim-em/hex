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

private theorem divModMonicModSquare_zero_mod_base
    (m : Nat) (p q qOut rOut : ZPoly)
    (hp : ZPoly.congr p 0 m)
    (hqr : (qOut, rOut) = divModMonicModSquare p q m) :
    ZPoly.congr qOut 0 m ∧ ZPoly.congr rOut 0 m := by
  sorry

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

private theorem quadraticHenselStep_bezout_correction_algebra
    (m : Nat)
    (g' h' s t b qBezout rBezout : ZPoly)
    (hm : 0 < m)
    (hb : ZPoly.congr b (s * g' + t * h' - 1) (m * m))
    (hdiv : ZPoly.congr (qBezout * g' + rBezout) (t * b) (m * m)) :
    let t' := subModSquare t rBezout m
    let s' := subModSquare (subModSquare s (mulModSquare s b m) m) (mulModSquare qBezout h' m) m
    ZPoly.congr (s' * g' + t' * h') (1 - b * b) (m * m) := by
  sorry

private theorem quadraticHenselStep_bezout_error_from_factor_update
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
