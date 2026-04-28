import HexHensel
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic

/-!
Initial coprimality-lifting infrastructure for `HexHenselMathlib`.

This module sets up the `Polynomial ℤ` statements that later Hensel-correctness
and uniqueness proofs need: coefficientwise divisibility transport through
`Polynomial.map`, compatibility of the reduction maps
`ZMod (p^(k+1)) → ZMod (p^k) → ZMod p`, the nilpotent-unit lemma for
`1 + p * u`, and the coprimality-lifting theorem surface itself.
-/

namespace HexHenselMathlib

open Polynomial

noncomputable section

/-- Reducing an integer coefficient modulo `p` gives zero exactly when `p` divides it. -/
theorem coeff_map_intCastRingHom_eq_zero_iff_dvd
    (f : Polynomial ℤ) (p n : ℕ) :
    (f.map (Int.castRingHom (ZMod p))).coeff n = 0 ↔ (p : ℤ) ∣ f.coeff n := by
  simp [Polynomial.coeff_map, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Equality after coefficientwise reduction modulo `p` is equivalent to divisibility of the coefficient difference. -/
theorem coeff_map_intCastRingHom_eq_iff_dvd_sub
    (f g : Polynomial ℤ) (p n : ℕ) :
    (f.map (Int.castRingHom (ZMod p))).coeff n =
        (g.map (Int.castRingHom (ZMod p))).coeff n ↔
      (p : ℤ) ∣ f.coeff n - g.coeff n := by
  rw [← sub_eq_zero, ← coeff_sub, ← Polynomial.map_sub]
  simpa using coeff_map_intCastRingHom_eq_zero_iff_dvd (f := f - g) p n

/-- Exact divisibility lets us recover an integer coefficient from its quotient. -/
theorem coeff_ediv_mul_eq_of_dvd {f : Polynomial ℤ} {m n : ℕ}
    (h : (m : ℤ) ∣ f.coeff n) :
    (f.coeff n / m) * m = f.coeff n := by
  exact Int.ediv_mul_cancel h

/-- Exact divisibility also gives the left-multiplication form used in coefficientwise quotient rewrites. -/
theorem coeff_mul_ediv_eq_of_dvd {f : Polynomial ℤ} {m n : ℕ}
    (h : (m : ℤ) ∣ f.coeff n) :
    (m : ℤ) * (f.coeff n / m) = f.coeff n := by
  rw [Int.mul_comm, Int.ediv_mul_cancel h]

/-- Reducing coefficients from `ZMod (p^(k+1))` to `ZMod p` agrees with direct reduction. -/
theorem zmod_castHom_comp_intCastRingHom_pow_succ
    (p k : ℕ) :
    (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)).comp
        (Int.castRingHom (ZMod (p ^ (k + 1)))) =
      Int.castRingHom (ZMod p) := by
  ext z
  simp

/-- Reducing coefficients from `ZMod (p^(k+1))` to `ZMod (p^k)` agrees with direct reduction. -/
theorem zmod_castHom_comp_intCastRingHom_pow_step
    (p k : ℕ) :
    (ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))).comp
        (Int.castRingHom (ZMod (p ^ (k + 1)))) =
      Int.castRingHom (ZMod (p ^ k)) := by
  ext z
  simp

/-- Polynomial reduction from `ZMod (p^(k+1))` to `ZMod p` is compatible with direct reduction. -/
theorem polynomial_map_zmod_pow_succ_to_base
    (f : Polynomial ℤ) (p k : ℕ) :
    (f.map (Int.castRingHom (ZMod (p ^ (k + 1))))).map
        (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)) =
      f.map (Int.castRingHom (ZMod p)) := by
  rw [map_map]
  simp [zmod_castHom_comp_intCastRingHom_pow_succ]

/-- Polynomial reduction from `ZMod (p^(k+1))` to `ZMod (p^k)` is compatible with direct reduction. -/
theorem polynomial_map_zmod_pow_succ_to_pow
    (f : Polynomial ℤ) (p k : ℕ) :
    (f.map (Int.castRingHom (ZMod (p ^ (k + 1))))).map
        (ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) =
      f.map (Int.castRingHom (ZMod (p ^ k))) := by
  rw [map_map]
  simp [zmod_castHom_comp_intCastRingHom_pow_step]

/-- In `Polynomial (ZMod (p^k))`, the correction term `p * u` is nilpotent, so `1 + p * u` is a unit. -/
theorem isUnit_one_add_C_mul
    (p k : ℕ) (u : Polynomial (ZMod (p ^ k))) :
    IsUnit (1 + Polynomial.C (p : ZMod (p ^ k)) * u) := by
  sorry

/-- Coprimality modulo `p` lifts to coprimality modulo `p^k`. -/
theorem coprime_mod_p_lifts (g h : Polynomial ℤ) (p : ℕ) (k : ℕ)
    [Fact (Nat.Prime p)] (hk : 0 < k) :
    IsCoprime (g.map (Int.castRingHom (ZMod p)))
              (h.map (Int.castRingHom (ZMod p))) →
    IsCoprime (g.map (Int.castRingHom (ZMod (p ^ k))))
              (h.map (Int.castRingHom (ZMod (p ^ k)))) := by
  sorry

end

end HexHenselMathlib
