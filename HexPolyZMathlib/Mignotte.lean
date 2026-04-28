import HexPolyZMathlib.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.NumberTheory.MahlerMeasure

/-!
Mignotte-bound infrastructure for integer polynomials.

This module packages the real-valued coefficient `l2norm` used by the
classical Mignotte bound together with the transport lemmas needed to move
between `Polynomial ℤ` and the complex-coefficient Mahler-measure API in
Mathlib.
-/

open scoped BigOperators

namespace HexPolyZMathlib

noncomputable section

/-- The Euclidean norm of the coefficient vector of an integer polynomial. -/
def l2norm (f : Polynomial ℤ) : ℝ :=
  Real.sqrt (∑ i ∈ f.support, (f.coeff i : ℝ) ^ 2)

@[simp]
theorem coeff_map_intCast (f : Polynomial ℤ) (n : Nat) :
    (f.map (Int.castRingHom ℂ)).coeff n = (f.coeff n : ℂ) := by
  simp

@[simp]
theorem natDegree_map_intCast (f : Polynomial ℤ) :
    (f.map (Int.castRingHom ℂ)).natDegree = f.natDegree := by
  simpa using
    (Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ)
      (hf := RingHom.injective_int (Int.castRingHom ℂ)) f)

@[simp]
theorem support_map_intCast (f : Polynomial ℤ) :
    (f.map (Int.castRingHom ℂ)).support = f.support := by
  simpa using
    (Polynomial.support_map_of_injective (f := Int.castRingHom ℂ) f
      (RingHom.injective_int (Int.castRingHom ℂ)))

@[simp]
theorem norm_coeff_map_intCast (f : Polynomial ℤ) (n : Nat) :
    ‖(f.map (Int.castRingHom ℂ)).coeff n‖ = (Int.natAbs (f.coeff n) : ℝ) := by
  simp [Complex.norm_intCast]

theorem sq_norm_coeff_map_intCast (f : Polynomial ℤ) (n : Nat) :
    ‖(f.map (Int.castRingHom ℂ)).coeff n‖ ^ 2 = (f.coeff n : ℝ) ^ 2 := by
  simp [Complex.norm_intCast, pow_two]

/-- Landau's inequality specialized to `Polynomial ℤ` via the complex cast. -/
theorem mahlerMeasure_le_l2norm (f : Polynomial ℤ) :
    (f.map (Int.castRingHom ℂ)).mahlerMeasure ≤ l2norm f := by
  simpa [l2norm, support_map_intCast, sq_norm_coeff_map_intCast] using
    Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff (f.map (Int.castRingHom ℂ))

/-- Mignotte's coefficient bound for integer polynomial factors, obtained by
combining Mathlib's Mahler-measure coefficient estimate with Landau's
inequality. -/
theorem mignotte_bound (f g : Polynomial ℤ) (hf : f ≠ 0) (hg : g ∣ f) (j : ℕ) :
    (Int.natAbs (g.coeff j) : ℝ) ≤ Nat.choose g.natDegree j * l2norm f := by
  rcases hg with ⟨h, rfl⟩
  have hh0 : h ≠ 0 := by
    intro hh
    apply hf
    simp [hh]
  have hcoeff :=
      Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure
        (n := j) (g := g.map (Int.castRingHom ℂ)) (h := h.map (Int.castRingHom ℂ))
        (Polynomial.one_le_mahlerMeasure_of_ne_zero hh0)
  calc
    (Int.natAbs (g.coeff j) : ℝ) = ‖(g.map (Int.castRingHom ℂ)).coeff j‖ := by
      exact (norm_coeff_map_intCast (f := g) (n := j)).symm
    _ ≤ Nat.choose (g.map (Int.castRingHom ℂ)).natDegree j *
          ((g.map (Int.castRingHom ℂ)) * (h.map (Int.castRingHom ℂ))).mahlerMeasure := hcoeff
    _ = Nat.choose g.natDegree j * (((g * h).map (Int.castRingHom ℂ)).mahlerMeasure) := by
      simp [Polynomial.map_mul]
    _ ≤ Nat.choose g.natDegree j * l2norm (g * h) := by
      gcongr
      exact mahlerMeasure_le_l2norm (f := g * h)

end

end HexPolyZMathlib
