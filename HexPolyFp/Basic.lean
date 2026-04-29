import HexModArith.Ring
import HexPoly.Euclid

/-!
Core definitions for executable polynomials over `F_p`.

This module specializes the generic dense-polynomial API to
`Hex.ZMod64 p`, exposing the `FpPoly p` abbreviation together with the
constructors and instances needed by downstream finite-field
algorithms.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

instance : Zero (ZMod64 p) where
  zero := ZMod64.zero

instance : One (ZMod64 p) where
  one := ZMod64.one

instance : Add (ZMod64 p) where
  add := ZMod64.add

instance : Sub (ZMod64 p) where
  sub := ZMod64.sub

instance : Mul (ZMod64 p) where
  mul := ZMod64.mul

instance : Div (ZMod64 p) where
  div a b := ZMod64.mul a (ZMod64.inv b)

instance : DecidableEq (ZMod64 p) := by
  intro a b
  if h : a.val = b.val then
    exact isTrue (by
      cases a
      cases b
      cases h
      simp)
  else
    exact isFalse (by
      intro hab
      apply h
      exact congrArg ZMod64.val hab)

end ZMod64

/-- Executable dense polynomials over the prime-field candidate `ZMod64 p`. -/
abbrev FpPoly (p : Nat) [ZMod64.Bounds p] := DensePoly (ZMod64 p)

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- Polynomial irreducibility over `F_p` phrased as the absence of nontrivial
factorizations inside the executable dense-polynomial model. -/
def Irreducible (f : FpPoly p) : Prop :=
  f ≠ 0 ∧
    ∀ a b : FpPoly p, a * b = f → a.degree? = some 0 ∨ b.degree? = some 0

/-- Build an `FpPoly` from raw coefficients, trimming trailing zero residues. -/
def ofCoeffs (coeffs : Array (ZMod64 p)) : FpPoly p :=
  DensePoly.ofCoeffs coeffs

/-- Constant polynomial in `F_p[x]`. -/
def C (c : ZMod64 p) : FpPoly p :=
  DensePoly.C c

/-- The polynomial indeterminate `X`. -/
def X : FpPoly p :=
  DensePoly.monomial 1 (1 : ZMod64 p)

/-- Reduction modulo a monic polynomial over `F_p[x]`. -/
def modByMonic (f g : FpPoly p) (hmonic : DensePoly.Monic f) : FpPoly p :=
  DensePoly.modByMonic g f hmonic

private theorem zmod_eq_of_toNat_eq {a b : ZMod64 p} (h : a.toNat = b.toNat) : a = b := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  simpa [ZMod64.toNat_eq_val] using h

private theorem zmod_add_zero (a : ZMod64 p) : a + 0 = a := by
  grind

private theorem zmod_zero_add (a : ZMod64 p) : 0 + a = a := by
  grind

private theorem zmod_mul_zero (a : ZMod64 p) : a * 0 = 0 := by
  grind

private theorem zmod_one_mul (a : ZMod64 p) : 1 * a = a := by
  grind

private theorem zmod_mul_one (a : ZMod64 p) : a * 1 = a := by
  grind

private theorem coeff_one (n : Nat) :
    (1 : FpPoly p).coeff n = if n = 0 then (1 : ZMod64 p) else 0 := by
  change (DensePoly.C (1 : ZMod64 p)).coeff n = if n = 0 then (1 : ZMod64 p) else 0
  exact DensePoly.coeff_C (1 : ZMod64 p) n

theorem add_zero (f : FpPoly p) :
    f + 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_add]
  grind

theorem zero_add (f : FpPoly p) :
    0 + f = f := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_add]
  grind

theorem add_comm (f g : FpPoly p) :
    f + g = g + f := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_add]
  grind

theorem add_assoc (f g h : FpPoly p) :
    f + g + h = f + (g + h) := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_add]
  grind

theorem neg_zero :
    -(0 : FpPoly p) = 0 := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_neg]
  grind

theorem add_left_neg (f : FpPoly p) :
    -f + f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_add, DensePoly.coeff_neg]
  grind

theorem add_right_neg (f : FpPoly p) :
    f + -f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_add, DensePoly.coeff_neg]
  grind

theorem sub_zero (f : FpPoly p) :
    f - 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_sub]
  grind

theorem zero_sub (f : FpPoly p) :
    0 - f = -f := by
  rfl

theorem sub_self (f : FpPoly p) :
    f - f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_sub]
  grind

theorem sub_eq_add_neg (f g : FpPoly p) :
    f - g = f + -g := by
  apply DensePoly.ext_coeff
  intro i
  simp [DensePoly.coeff_add, DensePoly.coeff_sub, DensePoly.coeff_neg]
  grind

@[simp] theorem zero_mul (f : FpPoly p) :
    0 * f = 0 := by
  rfl

@[simp] theorem mul_zero (f : FpPoly p) :
    f * 0 = 0 := by
  change DensePoly.mul f (0 : FpPoly p) = 0
  unfold DensePoly.mul
  have hstep (acc : FpPoly p) (i : Nat) :
      acc + DensePoly.shift i (DensePoly.scale (f.coeff i) (0 : FpPoly p)) = acc := by
    simpa [DensePoly.scale, DensePoly.shift] using add_zero acc
  have hfold :
      ∀ xs : List Nat, ∀ acc : FpPoly p,
        xs.foldl
            (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) (0 : FpPoly p)))
            acc = acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        rfl
    | cons i xs ih =>
        intro acc
        simp [List.foldl_cons, hstep acc i, ih]
  simpa using hfold (List.range f.size) 0

private theorem coeff_mul_one_fold (f : FpPoly p) (n k : Nat) :
    ((List.range n).foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) (1 : FpPoly p)))
        (0 : FpPoly p)).coeff k =
      if k < n then f.coeff k else 0 := by
  induction n with
  | zero =>
      exact DensePoly.coeff_zero k
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [DensePoly.coeff_add, ih]
      rw [DensePoly.coeff_shift_scale]
      · rw [coeff_one]
        by_cases hk : k < n
        · have hks : k < n + 1 := Nat.lt_trans hk (Nat.lt_succ_self n)
          simp [hk, hks]
          exact zmod_add_zero (f.coeff k)
        · by_cases hkn : k = n
          · subst k
            simp [zmod_mul_one]
            exact zmod_zero_add (f.coeff n)
          · have hks : ¬ k < n + 1 := by omega
            have hsub : k - n ≠ 0 := by omega
            simp [hk, hks, hsub, zmod_mul_zero]
            exact zmod_zero_add (0 : ZMod64 p)
      · exact zmod_mul_zero (f.coeff n)

@[simp] theorem one_mul (f : FpPoly p) :
    1 * f = f := by
  change DensePoly.mul (1 : FpPoly p) f = f
  unfold DensePoly.mul
  have hle : (1 : FpPoly p).size ≤ 1 := by
    change (DensePoly.C (1 : ZMod64 p)).size ≤ 1
    exact DensePoly.size_C_le_one (1 : ZMod64 p)
  apply DensePoly.ext_coeff
  intro k
  rcases Nat.eq_zero_or_pos (1 : FpPoly p).size with hzero | hpos
  · have hone : (1 : ZMod64 p) = 0 := by
      have hcoeff :
          (1 : FpPoly p).coeff 0 = (0 : ZMod64 p) :=
        DensePoly.coeff_eq_zero_of_size_le (1 : FpPoly p) (i := 0) (by omega)
      simpa [coeff_one] using hcoeff
    have hf : f.coeff k = (0 : ZMod64 p) := by
      have hpdiv : p ∣ 1 := (ZMod64.natCast_eq_zero_iff_dvd (p := p) 1).mp hone
      have hpone : p = 1 := Nat.dvd_one.mp hpdiv
      apply zmod_eq_of_toNat_eq
      have hnat : (f.coeff k).toNat = 0 :=
        by
          have hlt : (f.coeff k).toNat < 1 := by simpa [hpone] using (f.coeff k).toNat_lt
          omega
      simpa using hnat
    rw [hzero]
    simp only [List.range_zero, List.foldl_nil]
    rw [hf]
    exact DensePoly.coeff_zero k
  · have hsize : (1 : FpPoly p).size = 1 := by omega
    rw [hsize]
    simp only [List.range_one, List.foldl_cons, List.foldl_nil]
    rw [DensePoly.coeff_add, DensePoly.coeff_shift_scale]
    · rw [coeff_one]
      simp [zmod_one_mul]
      exact zmod_zero_add (f.coeff k)
    · exact zmod_mul_zero ((1 : FpPoly p).coeff 0)

@[simp] theorem mul_one (f : FpPoly p) :
    f * 1 = f := by
  change DensePoly.mul f (1 : FpPoly p) = f
  unfold DensePoly.mul
  apply DensePoly.ext_coeff
  intro k
  rw [coeff_mul_one_fold]
  by_cases hk : k < f.size
  · simp [hk]
  · have hf : f.coeff k = (0 : ZMod64 p) :=
      DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hk)
    simp [hk, hf]

end FpPoly
end Hex
