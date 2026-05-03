import HexModArith.Prime
import HexPoly.Euclid
import Init.Data.List.Lemmas
import Init.Data.List.Perm

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

/-- Typeclass wrapper for the prime-modulus assumption needed by field-style polynomial
division laws over `ZMod64 p`. -/
class PrimeModulus (p : Nat) : Prop where
  prime : Hex.Nat.Prime p

/-- Build the prime-modulus typeclass witness from an explicit project-local primality proof. -/
@[reducible]
def primeModulusOfPrime (hp : Hex.Nat.Prime p) : PrimeModulus p :=
  ⟨hp⟩

private theorem divMod_spec_core (f g : DensePoly (ZMod64 p)) :
    let qr := DensePoly.divMod f g
    qr.1 * g + qr.2 = f := by
  sorry

private theorem mod_sub_self_eq_mul_neg_div (f m : DensePoly (ZMod64 p)) :
    f % m - f = m * (0 - (f / m)) := by
  have hdiv : (f / m) * m + (f % m) = f := by
    simpa [DensePoly.div, DensePoly.mod] using divMod_spec_core f m
  calc
    f % m - f = 0 - (f / m) * m := by
      apply DensePoly.ext_coeff
      intro n
      have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hdiv
      have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
      have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
      change (((f / m) * m + (f % m)).coeff n = f.coeff n) at hcoeff
      rw [DensePoly.coeff_add ((f / m) * m) (f % m) n hzero_add] at hcoeff
      rw [DensePoly.coeff_sub (f % m) f n hzero_sub]
      rw [DensePoly.coeff_sub 0 ((f / m) * m) n hzero_sub]
      rw [DensePoly.coeff_zero]
      grind
    _ = m * (0 - (f / m)) := by
      exact (DensePoly.mul_sub_zero_comm m (f / m)).symm

private theorem congr_mod_core (f m : DensePoly (ZMod64 p)) :
    DensePoly.Congr (f % m) f m := by
  exact ⟨0 - (f / m), mod_sub_self_eq_mul_neg_div f m⟩

private theorem eq_add_mul_of_sub_eq_mul {f g m r : DensePoly (ZMod64 p)}
    (hsub : f - g = m * r) :
    f = g + m * r := by
  apply DensePoly.ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hsub
  have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
  have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  change (f - g).coeff n = (m * r).coeff n at hcoeff
  rw [DensePoly.coeff_sub f g n hzero_sub] at hcoeff
  rw [DensePoly.coeff_add g (m * r) n hzero_add]
  grind

private theorem add_sub_add_right (a b c d : DensePoly (ZMod64 p)) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
  have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_sub (a + b) (c + d) n hzero_sub]
  rw [DensePoly.coeff_add a b n hzero_add, DensePoly.coeff_add c d n hzero_add]
  rw [DensePoly.coeff_add (a - c) (b - d) n hzero_add]
  rw [DensePoly.coeff_sub a c n hzero_sub, DensePoly.coeff_sub b d n hzero_sub]
  grind

private theorem divMod_remainder_degree_lt_core
    [PrimeModulus p] (f m : DensePoly (ZMod64 p))
    (hdegree : 0 < m.degree?.getD 0) :
    (DensePoly.divMod f m).2.degree?.getD 0 < m.degree?.getD 0 := by
  sorry

private theorem mod_remainder_degree_lt_core
    [PrimeModulus p] (f m : DensePoly (ZMod64 p))
    (hdegree : 0 < m.degree?.getD 0) :
    (f % m).degree?.getD 0 < m.degree?.getD 0 := by
  simpa [DensePoly.mod] using divMod_remainder_degree_lt_core f m hdegree

private theorem canonical_remainder_unique_of_pos_degree
    (r s m : DensePoly (ZMod64 p))
    (hr : r.degree?.getD 0 < m.degree?.getD 0)
    (hs : s.degree?.getD 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr r s m) :
    r = s := by
  sorry

private theorem mod_remainders_congr_of_congr (f g m : DensePoly (ZMod64 p))
    (hcongr : DensePoly.Congr f g m) :
    DensePoly.Congr (f % m) (g % m) m := by
  rcases congr_mod_core f m with ⟨rf, hf⟩
  rcases congr_mod_core g m with ⟨rg, hg⟩
  rcases hcongr with ⟨q, hq⟩
  refine ⟨(q + rf) + (0 - rg), ?_⟩
  have hf_add : f % m = f + m * rf := eq_add_mul_of_sub_eq_mul hf
  have hg_add : g % m = g + m * rg := eq_add_mul_of_sub_eq_mul hg
  have hneg_mul : (0 : DensePoly (ZMod64 p)) - m * rg =
      m * ((0 : DensePoly (ZMod64 p)) - rg) := by
    calc
      (0 : DensePoly (ZMod64 p)) - m * rg =
          (0 : DensePoly (ZMod64 p)) - rg * m := by
        exact congrArg (fun x : DensePoly (ZMod64 p) => (0 : DensePoly (ZMod64 p)) - x)
          (DensePoly.mul_comm_poly m rg)
      _ = m * ((0 : DensePoly (ZMod64 p)) - rg) := by
        exact (DensePoly.mul_sub_zero_comm m rg).symm
  calc
    (f % m) - (g % m)
        = (f + m * rf) - (g + m * rg) := by rw [hf_add, hg_add]
    _ = (f - g) + ((m * rf) - (m * rg)) := by
      exact add_sub_add_right f (m * rf) g (m * rg)
    _ = m * q + ((m * rf) - (m * rg)) := by rw [hq]
    _ = m * q + (m * rf + ((0 : DensePoly (ZMod64 p)) - m * rg)) := by
      exact congrArg (fun x : DensePoly (ZMod64 p) => m * q + x)
        (DensePoly.sub_eq_add_neg_poly (m * rf) (m * rg))
    _ = m * q + (m * rf + m * ((0 : DensePoly (ZMod64 p)) - rg)) := by rw [hneg_mul]
    _ = (m * q + m * rf) + m * ((0 : DensePoly (ZMod64 p)) - rg) := by
      exact (DensePoly.add_assoc_poly (m * q) (m * rf)
        (m * ((0 : DensePoly (ZMod64 p)) - rg))).symm
    _ = m * (q + rf) + m * ((0 : DensePoly (ZMod64 p)) - rg) := by
      exact congrArg
        (fun x : DensePoly (ZMod64 p) => x + m * ((0 : DensePoly (ZMod64 p)) - rg))
        (DensePoly.mul_add_right_poly m q rf).symm
    _ = m * ((q + rf) + ((0 : DensePoly (ZMod64 p)) - rg)) := by
      exact (DensePoly.mul_add_right_poly m (q + rf)
        ((0 : DensePoly (ZMod64 p)) - rg)).symm

private theorem mod_eq_mod_of_congr_pos_degree
    [PrimeModulus p] (f g m : DensePoly (ZMod64 p))
    (hdegree : 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr f g m) :
    f % m = g % m := by
  apply canonical_remainder_unique_of_pos_degree
  · exact mod_remainder_degree_lt_core f m hdegree
  · exact mod_remainder_degree_lt_core g m hdegree
  · exact mod_remainders_congr_of_congr f g m hcongr

private theorem mod_eq_mod_of_congr_not_pos_degree (f g m : DensePoly (ZMod64 p))
    (hdegree : ¬ 0 < m.degree?.getD 0)
    (hcongr : DensePoly.Congr f g m) :
    f % m = g % m := by
  sorry

private theorem mod_eq_mod_of_congr_core
    [PrimeModulus p] (f g m : DensePoly (ZMod64 p))
    (hcongr : DensePoly.Congr f g m) :
    f % m = g % m := by
  by_cases hdegree : 0 < m.degree?.getD 0
  · exact mod_eq_mod_of_congr_pos_degree f g m hdegree hcongr
  · exact mod_eq_mod_of_congr_not_pos_degree f g m hdegree hcongr

private theorem sub_self_right_add (a b : DensePoly (ZMod64 p)) :
    (a + b) - a = b := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
  have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_sub (a + b) a n hzero_sub]
  rw [DensePoly.coeff_add a b n hzero_add]
  grind

private theorem mul_left_remainder_delta (f g m rf rg : DensePoly (ZMod64 p))
    (hf : f % m = f + m * rf)
    (hg : g % m = g + m * rg) :
    (f % m * (g % m)) - (f * g) = m * (rf * (g % m) + f * rg) := by
  have hleft :
      (f + m * rf) * (g % m) =
        f * (g % m) + (m * rf) * (g % m) :=
    DensePoly.mul_add_left_poly f (m * rf) (g % m)
  have hright :
      f * (g % m) = f * g + f * (m * rg) := by
    rw [hg]
    exact DensePoly.mul_add_right_poly f g (m * rg)
  calc
    (f % m * (g % m)) - (f * g)
        = ((f + m * rf) * (g % m)) - (f * g) := by rw [hf]
    _ = (f * (g % m) + (m * rf) * (g % m)) - (f * g) := by rw [hleft]
    _ = ((f * g + f * (m * rg)) + (m * rf) * (g % m)) - (f * g) := by
      rw [hright]
    _ = (f * g + (f * (m * rg) + (m * rf) * (g % m))) - (f * g) := by
      exact congrArg (fun x => x - f * g)
        (DensePoly.add_assoc_poly (f * g) (f * (m * rg)) ((m * rf) * (g % m)))
    _ = f * (m * rg) + (m * rf) * (g % m) := by
      rw [sub_self_right_add]
    _ = m * (f * rg) + (m * rf) * (g % m) := by
      apply congrArg (fun x => x + (m * rf) * (g % m))
      calc
        f * (m * rg) = (f * m) * rg := by
          exact (DensePoly.mul_assoc_poly f m rg).symm
        _ = (m * f) * rg := by
          exact congrArg (fun x => x * rg) (DensePoly.mul_comm_poly f m)
        _ = m * (f * rg) := by
          exact DensePoly.mul_assoc_poly m f rg
    _ = m * (f * rg) + m * (rf * (g % m)) := by
      exact congrArg (fun x => m * (f * rg) + x)
        (DensePoly.mul_assoc_poly m rf (g % m))
    _ = m * (f * rg + rf * (g % m)) := by
      exact (DensePoly.mul_add_right_poly m (f * rg) (rf * (g % m))).symm
    _ = m * (rf * (g % m) + f * rg) := by
      exact congrArg (fun x => m * x)
        (DensePoly.add_comm_poly (f * rg) (rf * (g % m)))

/-- The `F_p[x]` division law obligations used by quotient constructions.

These are the concrete finite-field instances of the generic `DensePoly.DivModLaws` proof
surface used by downstream quotient-ring code; the executable division operations
themselves are inherited from `DensePoly`. -/
instance instDivModLawsZMod64Fp (p : Nat) [Bounds p] [PrimeModulus p] :
    DensePoly.DivModLaws (ZMod64 p) where
  divMod_spec := by
    intro f g
    exact divMod_spec_core f g
  divMod_remainder_degree_lt_of_pos_degree := by
    intro f g hdegree
    exact divMod_remainder_degree_lt_core f g hdegree
  divModMonic_eq_divMod_of_monic := by
    intro f g hmonic
    sorry
  mod_self_eq_zero := by
    intro f
    sorry
  mod_eq_zero_of_dvd := by
    intro f g hdiv
    sorry
  mod_mod_of_not_pos_degree := by
    intro f g hdegree
    sorry
  mod_eq_mod_of_congr := by
    intro f g m hcongr
    exact mod_eq_mod_of_congr_core f g m hcongr
  mod_add_mod := by
    intro f g m
    apply Eq.symm
    apply mod_eq_mod_of_congr_core
    rcases congr_mod_core f m with ⟨rf, hf⟩
    rcases congr_mod_core g m with ⟨rg, hg⟩
    exact ⟨rf + rg, by
      calc
        (f % m + g % m) - (f + g)
            = (f % m - f) + (g % m - g) := add_sub_add_right (f % m) (g % m) f g
        _ = m * rf + m * rg := by rw [hf, hg]
        _ = m * (rf + rg) := by exact (DensePoly.mul_add_right_poly m rf rg).symm⟩
  mod_mul_mod := by
    intro f g m
    apply Eq.symm
    apply mod_eq_mod_of_congr_core
    rcases congr_mod_core f m with ⟨rf, hf⟩
    rcases congr_mod_core g m with ⟨rg, hg⟩
    exact ⟨rf * (g % m) + f * rg, by
      have hf' : f % m = f + m * rf := by
        apply DensePoly.ext_coeff
        intro n
        have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hf
        have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
        have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
        change (f % m - f).coeff n = (m * rf).coeff n at hcoeff
        rw [DensePoly.coeff_sub (f % m) f n hzero_sub] at hcoeff
        rw [DensePoly.coeff_add f (m * rf) n hzero_add]
        grind
      have hg' : g % m = g + m * rg := by
        apply DensePoly.ext_coeff
        intro n
        have hcoeff := congrArg (fun x : DensePoly (ZMod64 p) => x.coeff n) hg
        have hzero_sub : (0 : ZMod64 p) - (0 : ZMod64 p) = 0 := by grind
        have hzero_add : (0 : ZMod64 p) + (0 : ZMod64 p) = 0 := by grind
        change (g % m - g).coeff n = (m * rg).coeff n at hcoeff
        rw [DensePoly.coeff_sub (g % m) g n hzero_sub] at hcoeff
        rw [DensePoly.coeff_add g (m * rg) n hzero_add]
        grind
      exact mul_left_remainder_delta f g m rf rg hf' hg'⟩

/-- The `F_p[x]` gcd law obligations used by finite-field inverse construction. -/
instance : DensePoly.GcdLaws (ZMod64 p) where
  gcd_dvd_left := by
    intro f g
    sorry
  gcd_dvd_right := by
    intro f g
    sorry
  dvd_gcd := by
    intro d f g hdf hdg
    sorry
  xgcd_bezout := by
    intro f g
    sorry

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

private theorem zmod_add_zero_zero :
    (Zero.zero : ZMod64 p) + (Zero.zero : ZMod64 p) = (Zero.zero : ZMod64 p) :=
  zmod_add_zero Zero.zero

private theorem zmod_sub_zero_zero :
    (Zero.zero : ZMod64 p) - (Zero.zero : ZMod64 p) = (Zero.zero : ZMod64 p) := by
  change ZMod64.sub (Zero.zero : ZMod64 p) Zero.zero = Zero.zero
  apply zmod_eq_of_toNat_eq
  change (ZMod64.sub (Zero.zero : ZMod64 p) Zero.zero).toNat =
    (Zero.zero : ZMod64 p).toNat
  rw [ZMod64.toNat_sub]
  have hz : (Zero.zero : ZMod64 p).val.toNat = 0 := by
    change (Zero.zero : ZMod64 p).toNat = 0
    exact ZMod64.toNat_zero
  simp [hz]

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
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem zero_add (f : FpPoly p) :
    0 + f = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem add_comm (f g : FpPoly p) :
    f + g = g + f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  grind

theorem add_assoc (f g h : FpPoly p) :
    f + g + h = f + (g + h) := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add (f + g) h i zmod_add_zero_zero]
  rw [DensePoly.coeff_add f (g + h) i zmod_add_zero_zero]
  rw [DensePoly.coeff_add f g i zmod_add_zero_zero]
  rw [DensePoly.coeff_add g h i zmod_add_zero_zero]
  grind

theorem neg_zero :
    -(0 : FpPoly p) = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_neg _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem add_left_neg (f : FpPoly p) :
    -f + f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_neg _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem add_right_neg (f : FpPoly p) :
    f + -f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_neg _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem sub_zero (f : FpPoly p) :
    f - 0 = f := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub _ _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem zero_sub (f : FpPoly p) :
    0 - f = -f := by
  rfl

theorem sub_self (f : FpPoly p) :
    f - f = 0 := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_sub _ _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_zero]
  grind

theorem sub_eq_add_neg (f g : FpPoly p) :
    f - g = f + -g := by
  apply DensePoly.ext_coeff
  intro i
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_sub _ _ _ zmod_sub_zero_zero]
  rw [DensePoly.coeff_neg _ _ zmod_sub_zero_zero]
  grind

@[simp] theorem zero_mul (f : FpPoly p) :
    0 * f = 0 := by
  rfl

@[simp] theorem mul_zero (f : FpPoly p) :
    f * 0 = 0 := by
  sorry

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
      rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero, ih]
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
  sorry

@[simp] theorem mul_one (f : FpPoly p) :
    f * 1 = f := by
  sorry
/-- The `i`th schoolbook contribution to coefficient `n` of `f * g`. -/
def mulCoeffTerm (f g : FpPoly p) (n i : Nat) : ZMod64 p :=
  if n < i then 0 else f.coeff i * g.coeff (n - i)

/-- The executable schoolbook coefficient sum matching `FpPoly` multiplication. -/
def mulCoeffSum (f g : FpPoly p) (n : Nat) : ZMod64 p :=
  (List.range f.size).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0

private theorem coeff_mul_fold (xs : List Nat) (acc f g : FpPoly p) (n : Nat) :
    (xs.foldl
        (fun acc i => acc + DensePoly.shift i (DensePoly.scale (f.coeff i) g))
        acc).coeff n =
      xs.foldl (fun coeff i => coeff + mulCoeffTerm f g n i) (acc.coeff n) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      have hzero : f.coeff i * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero,
        DensePoly.coeff_shift_scale i (f.coeff i) g n hzero]
      rfl

theorem coeff_mul (f g : FpPoly p) (n : Nat) :
    (f * g).coeff n = mulCoeffSum f g n := by
  sorry

private theorem mulCoeffTerm_eq_zero_of_size_le
    (f g : FpPoly p) (n i : Nat) (hi : f.size ≤ i) :
    mulCoeffTerm f g n i = 0 := by
  unfold mulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
  · have hcoeff : f.coeff i = 0 := DensePoly.coeff_eq_zero_of_size_le f hi
    simp [hn, hcoeff]
    grind

private theorem fold_mulCoeff_extend (f g : FpPoly p) (n d : Nat) :
    (List.range (f.size + d)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range f.size).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : mulCoeffTerm f g n (f.size + d) = 0 :=
        mulCoeffTerm_eq_zero_of_size_le f g n (f.size + d) (by omega)
      simp [hterm]
      grind

private theorem mulCoeffSum_eq_bound
    (f g : FpPoly p) (n m : Nat) (hm : f.size ≤ m) :
    mulCoeffSum f g n =
      (List.range m).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  unfold mulCoeffSum
  have hm' : f.size + (m - f.size) = m := by omega
  rw [← hm', fold_mulCoeff_extend]

private theorem coeff_mul_of_size_le
    (f g : FpPoly p) (n m : Nat) (hm : f.size ≤ m) :
    (f * g).coeff n =
      (List.range m).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  rw [coeff_mul, mulCoeffSum_eq_bound f g n m hm]

private theorem mulCoeffTerm_eq_zero_of_degree_lt
    (f g : FpPoly p) (n i : Nat) (hi : n < i) :
    mulCoeffTerm f g n i = 0 := by
  simp [mulCoeffTerm, hi]

private theorem fold_mulCoeff_truncate_degree
    (f g : FpPoly p) (n d : Nat) :
    (List.range (n + 1 + d)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hterm : mulCoeffTerm f g n (n + 1 + d) = 0 :=
        mulCoeffTerm_eq_zero_of_degree_lt f g n (n + 1 + d) (by omega)
      simp [hterm]
      grind

private theorem mulCoeffSum_eq_degree_bound
    (f g : FpPoly p) (n : Nat) :
    mulCoeffSum f g n =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
  unfold mulCoeffSum
  by_cases hsize : f.size ≤ n + 1
  · exact mulCoeffSum_eq_bound f g n (n + 1) hsize
  · have hle : n + 1 ≤ f.size := Nat.le_of_not_ge hsize
    have hsize' : n + 1 + (f.size - (n + 1)) = f.size := by omega
    rw [← hsize']
    exact fold_mulCoeff_truncate_degree f g n (f.size - (n + 1))

private theorem fold_add_right
    (xs : List (ZMod64 p)) (a b : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) (a + b) =
      xs.foldl (fun acc x => acc + x) a + b := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hacc : a + b + x = (a + x) + b := by grind
      rw [hacc]
      exact ih (a + x)

private theorem fold_add_reverse
    (xs : List (ZMod64 p)) (a : ZMod64 p) :
    xs.reverse.foldl (fun acc x => acc + x) a =
      xs.foldl (fun acc x => acc + x) a := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      rw [fold_add_right xs a x]

private theorem range_succ_reverse_eq_map_sub (n : Nat) :
    (List.range (n + 1)).reverse = (List.range (n + 1)).map (fun i => n - i) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [List.length_reverse] at hleft hright
    rw [List.getElem_reverse]
    simp [List.getElem_map, List.getElem_range]

private theorem mulCoeffTerm_comm_reindex
    (f g : FpPoly p) (n i : Nat) (hi : i < n + 1) :
    mulCoeffTerm f g n (n - i) = mulCoeffTerm g f n i := by
  have hile : i ≤ n := by omega
  have hleft : ¬ n < n - i := by omega
  have hright : ¬ n < i := by omega
  simp [mulCoeffTerm, hleft, hright, Nat.sub_sub_self hile]
  grind

private theorem fold_mulCoeff_comm_reindex_list
    (f g : FpPoly p) (n : Nat) (xs : List Nat)
    (hxs : ∀ i, i ∈ xs → i < n + 1) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + mulCoeffTerm f g n (n - i)) acc =
      xs.foldl (fun acc i => acc + mulCoeffTerm g f n i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hi : i < n + 1 := hxs i (by simp)
      rw [mulCoeffTerm_comm_reindex f g n i hi]
      exact ih (by
        intro j hj
        exact hxs j (by simp [hj])) (acc + mulCoeffTerm g f n i)

private theorem fold_mulCoeff_comm
    (f g : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
      (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm g f n i) 0 := by
  have hrev :
      (List.range (n + 1)).reverse.foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 =
        (List.range (n + 1)).foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 := by
    simpa [List.foldl_map, ← List.map_reverse] using
      fold_add_reverse (p := p)
        ((List.range (n + 1)).map (fun i => mulCoeffTerm f g n i)) 0
  rw [← hrev]
  rw [range_succ_reverse_eq_map_sub]
  rw [List.foldl_map]
  exact fold_mulCoeff_comm_reindex_list f g n (List.range (n + 1)) (by
    intro i hi
    exact List.mem_range.mp hi) 0

theorem mul_comm (f g : FpPoly p) :
    f * g = g * f := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_degree_bound f g n]
  rw [mulCoeffSum_eq_degree_bound g f n]
  exact fold_mulCoeff_comm f g n

private theorem mulCoeffTerm_left_distrib (f g h : FpPoly p) (n i : Nat) :
    mulCoeffTerm f (g + h) n i =
      mulCoeffTerm f g n i + mulCoeffTerm f h n i := by
  unfold mulCoeffTerm
  by_cases hi : n < i
  · simp [hi]
    grind
  · rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
    simp [hi]
    grind

private theorem mulCoeffTerm_right_distrib (f g h : FpPoly p) (n i : Nat) :
    mulCoeffTerm (f + g) h n i =
      mulCoeffTerm f h n i + mulCoeffTerm g h n i := by
  unfold mulCoeffTerm
  by_cases hi : n < i
  · simp [hi]
    grind
  · rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
    simp [hi]
    grind

private theorem fold_distrib_acc
    (xs : List Nat) (a b : ZMod64 p)
    (term term₁ term₂ : Nat → ZMod64 p)
    (hterm : ∀ i, term i = term₁ i + term₂ i) :
    xs.foldl (fun acc i => acc + term i) (a + b) =
      xs.foldl (fun acc i => acc + term₁ i) a +
        xs.foldl (fun acc i => acc + term₂ i) b := by
  induction xs generalizing a b with
  | nil =>
      rfl
  | cons i xs ih =>
    simp only [List.foldl_cons]
    rw [hterm i]
    have hacc :
        a + b + (term₁ i + term₂ i) =
          (a + term₁ i) + (b + term₂ i) := by
      grind
    rw [hacc]
    exact ih (a + term₁ i) (b + term₂ i)

private theorem fold_mul_right
    (xs : List Nat) (term : Nat → ZMod64 p) (c : ZMod64 p) :
    xs.foldl (fun acc i => acc + term i) 0 * c =
      xs.foldl (fun acc i => acc + term i * c) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hfold :
          xs.foldl (fun acc j => acc + term j) (0 + term i) =
            xs.foldl (fun acc j => acc + term j) 0 + term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map term) 0 (term i)
      have hfold' :
          xs.foldl (fun acc j => acc + term j * c) (0 + term i * c) =
            xs.foldl (fun acc j => acc + term j * c) 0 + term i * c := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map (fun j => term j * c)) 0 (term i * c)
      calc
        xs.foldl (fun acc j => acc + term j) (0 + term i) * c
            = (xs.foldl (fun acc j => acc + term j) 0 + term i) * c := by
                rw [hfold]
        _ = xs.foldl (fun acc j => acc + term j) 0 * c + term i * c := by
                grind
        _ = xs.foldl (fun acc j => acc + term j * c) 0 + term i * c := by
                rw [ih]
        _ = xs.foldl (fun acc j => acc + term j * c) (0 + term i * c) := by
                rw [hfold']

private theorem fold_mul_left
    (xs : List Nat) (term : Nat → ZMod64 p) (c : ZMod64 p) :
    c * xs.foldl (fun acc i => acc + term i) 0 =
      xs.foldl (fun acc i => acc + c * term i) 0 := by
  induction xs with
  | nil =>
      grind
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hfold :
          xs.foldl (fun acc j => acc + term j) (0 + term i) =
            xs.foldl (fun acc j => acc + term j) 0 + term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map term) 0 (term i)
      have hfold' :
          xs.foldl (fun acc j => acc + c * term j) (0 + c * term i) =
            xs.foldl (fun acc j => acc + c * term j) 0 + c * term i := by
        simpa [List.foldl_map] using
          fold_add_right (p := p) (xs.map (fun j => c * term j)) 0 (c * term i)
      calc
        c * xs.foldl (fun acc j => acc + term j) (0 + term i)
            = c * (xs.foldl (fun acc j => acc + term j) 0 + term i) := by
                rw [hfold]
        _ = c * xs.foldl (fun acc j => acc + term j) 0 + c * term i := by
                grind
        _ = xs.foldl (fun acc j => acc + c * term j) 0 + c * term i := by
                rw [ih]
        _ = xs.foldl (fun acc j => acc + c * term j) (0 + c * term i) := by
                rw [hfold']

private theorem mulCoeffTerm_mul_left_expand
    (f g h : FpPoly p) (n i : Nat) (hi : ¬ n < i) :
    mulCoeffTerm (f * g) h n i =
      (List.range (i + 1)).foldl
        (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0 := by
  unfold mulCoeffTerm
  simp [hi]
  rw [coeff_mul, mulCoeffSum_eq_degree_bound f g i]
  exact fold_mul_right (p := p) (List.range (i + 1))
    (fun j => mulCoeffTerm f g i j) (h.coeff (n - i))

private theorem mulCoeffTerm_mul_right_expand
    (f g h : FpPoly p) (n i : Nat) (hi : ¬ n < i) :
    mulCoeffTerm f (g * h) n i =
      (List.range (n - i + 1)).foldl
        (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0 := by
  unfold mulCoeffTerm
  simp [hi]
  rw [coeff_mul, mulCoeffSum_eq_degree_bound g h (n - i)]
  exact fold_mul_left (p := p) (List.range (n - i + 1))
    (fun j => mulCoeffTerm g h (n - i) j) (f.coeff i)

private def leftAssocTriples (n : Nat) : List ((Nat × Nat) × Nat) :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range (i + 1)).map fun j => ((j, i - j), n - i)

private def rightAssocTriples (n : Nat) : List ((Nat × Nat) × Nat) :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range (n - i + 1)).map fun j => ((i, j), n - i - j)

private theorem nodup_map_of_injective
    {α β : Type} {xs : List α} {f : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hxy' : x = y := hinj x (by simp) y (by simp [hy]) hxy.symm
        exact hxs.1 (by simpa [hxy'] using hy)
      · exact ih hxs.2 (by
          intro a ha b hb hab
          exact hinj a (by simp [ha]) b (by simp [hb]) hab)

private theorem nodup_flatMap_of_disjoint
    {α β : Type} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup)
    (hrow : ∀ x, x ∈ xs → (f x).Nodup)
    (hdisj :
      ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
        ∀ z, z ∈ f x → z ∈ f y → False) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨hrow x (by simp), ?_, ?_⟩
      · exact ih hxs.2
          (by intro y hy; exact hrow y (by simp [hy]))
          (by
            intro y hy z hz hyz t hty htz
            exact hdisj y (by simp [hy]) z (by simp [hz]) hyz t hty htz)
      · intro a ha b hb hab
        rcases List.mem_flatMap.mp hb with ⟨y, hy, hby⟩
        exact hdisj x (by simp) y (by simp [hy]) (by
          intro hxy
          exact hxs.1 (hxy ▸ hy)) a ha (hab ▸ hby)

private theorem leftAssocTriples_nodup (n : Nat) :
    (leftAssocTriples n).Nodup := by
  unfold leftAssocTriples
  apply nodup_flatMap_of_disjoint List.nodup_range
  · intro i hi
    apply nodup_map_of_injective List.nodup_range
    intro a ha b hb hab
    injection hab with hfst _
    exact Prod.ext_iff.mp hfst |>.1
  · intro i hi k hk hik z hzi hzk
    rcases List.mem_map.mp hzi with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨b, hb, hEq⟩
    injection hEq with hpair hlast
    injection hpair with hfirst hsecond
    have hi' : i < n + 1 := List.mem_range.mp hi
    have hk' : k < n + 1 := List.mem_range.mp hk
    omega

private theorem rightAssocTriples_nodup (n : Nat) :
    (rightAssocTriples n).Nodup := by
  unfold rightAssocTriples
  apply nodup_flatMap_of_disjoint List.nodup_range
  · intro i hi
    apply nodup_map_of_injective List.nodup_range
    intro a ha b hb hab
    injection hab with hfst _
    exact Prod.ext_iff.mp hfst |>.2
  · intro i hi k hk hik z hzi hzk
    rcases List.mem_map.mp hzi with ⟨a, ha, rfl⟩
    rcases List.mem_map.mp hzk with ⟨b, hb, hEq⟩
    injection hEq with hpair _
    exact hik (Prod.ext_iff.mp hpair |>.1).symm

private theorem leftAssocTriples_mem_iff (n : Nat) (abc : (Nat × Nat) × Nat) :
    abc ∈ leftAssocTriples n ↔ abc.1.1 + abc.1.2 + abc.2 = n := by
  rcases abc with ⟨⟨a, b⟩, c⟩
  simp [leftAssocTriples]
  constructor
  · intro h
    omega
  · intro h
    refine ⟨a + b, ?_, a, ?_, ?_⟩ <;> omega

private theorem rightAssocTriples_mem_iff (n : Nat) (abc : (Nat × Nat) × Nat) :
    abc ∈ rightAssocTriples n ↔ abc.1.1 + abc.1.2 + abc.2 = n := by
  rcases abc with ⟨⟨a, b⟩, c⟩
  simp [rightAssocTriples]
  constructor
  · intro h
    omega
  · intro h
    refine ⟨a, ?_, b, ?_, ?_⟩ <;> omega

private theorem leftAssocTriples_perm_rightAssocTriples (n : Nat) :
    List.Perm (leftAssocTriples n) (rightAssocTriples n) := by
  rw [List.perm_iff_count]
  intro abc
  rw [(leftAssocTriples_nodup n).count, (rightAssocTriples_nodup n).count]
  simp [leftAssocTriples_mem_iff, rightAssocTriples_mem_iff]

private theorem fold_add_perm {xs ys : List (ZMod64 p)}
    (h : List.Perm xs ys) (acc : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) acc =
      ys.foldl (fun acc x => acc + x) acc := by
  induction h generalizing acc with
  | nil =>
      rfl
  | cons x _ ih =>
      simp only [List.foldl_cons]
      exact ih (acc + x)
  | swap x y _ =>
      simp only [List.foldl_cons]
      have hxy : acc + x + y = acc + y + x := by grind
      rw [hxy]
  | trans _ _ ih₁ ih₂ =>
      exact Eq.trans (ih₁ acc) (ih₂ acc)

private theorem fold_add_acc
    (xs : List (ZMod64 p)) (acc : ZMod64 p) :
    xs.foldl (fun acc x => acc + x) acc =
      acc + xs.foldl (fun acc x => acc + x) 0 := by
  have h := fold_add_right (p := p) xs 0 acc
  simp only [zmod_zero_add] at h
  rw [h]
  grind

private theorem fold_flatMap_map_add
    {α β : Type} (xs : List α) (row : α → List β)
    (term : α → β → ZMod64 p) (acc : ZMod64 p) :
    (xs.flatMap fun x => (row x).map (term x)).foldl
        (fun acc x => acc + x) acc =
      xs.foldl
        (fun acc x =>
          acc + (row x).foldl (fun acc y => acc + term x y) 0) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, List.foldl_append]
      rw [fold_add_acc (p := p) ((row x).map (term x)) acc]
      rw [ih]
      simp [List.foldl_map]

private theorem fold_triangular_assoc_reindex
    (n : Nat) (term : Nat → Nat → Nat → ZMod64 p) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + term j (i - j) (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + term i j (n - i - j)) 0) 0 := by
  have hperm :
      List.Perm
        ((leftAssocTriples n).map (fun abc => term abc.1.1 abc.1.2 abc.2))
        ((rightAssocTriples n).map (fun abc => term abc.1.1 abc.1.2 abc.2)) :=
    (leftAssocTriples_perm_rightAssocTriples n).map _
  have hfold := fold_add_perm (p := p) hperm 0
  rw [← fold_flatMap_map_add (p := p) (List.range (n + 1))
    (fun i => List.range (i + 1))
    (fun i j => term j (i - j) (n - i)) 0]
  rw [← fold_flatMap_map_add (p := p) (List.range (n + 1))
    (fun i => List.range (n - i + 1))
    (fun i j => term i j (n - i - j)) 0]
  simpa [leftAssocTriples, rightAssocTriples, List.map_flatMap] using hfold

private theorem fold_add_congr
    (xs : List Nat) {term₁ term₂ : Nat → ZMod64 p}
    (hterm : ∀ i, i ∈ xs → term₁ i = term₂ i) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + term₁ i) acc =
      xs.foldl (fun acc i => acc + term₂ i) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hterm i (by simp)]
      exact ih (by
        intro j hj
        exact hterm j (by simp [hj])) (acc + term₂ i)

private theorem fold_add_zero_terms_acc
    (xs : List Nat) (term : Nat → ZMod64 p)
    (hterm : ∀ i, i ∈ xs → term i = 0) (acc : ZMod64 p) :
    xs.foldl (fun acc i => acc + term i) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [hterm i (by simp)]
      rw [zmod_add_zero]
      exact ih (by
        intro j hj
        exact hterm j (by simp [hj])) acc

private theorem fold_add_zero_terms
    (xs : List Nat) (term : Nat → ZMod64 p)
    (hterm : ∀ i, i ∈ xs → term i = 0) :
    xs.foldl (fun acc i => acc + term i) 0 = 0 := by
  exact fold_add_zero_terms_acc xs term hterm 0

private theorem fold_add_single_range
    (n t : Nat) (a : ZMod64 p) (ht : t < n + 1) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + if i = t then a else 0) 0 = a := by
  induction n with
  | zero =>
      have ht0 : t = 0 := by omega
      simp [ht0]
      exact zmod_zero_add a
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hlast : t = n + 1
      · subst t
        have hzero :
            (List.range (n + 1)).foldl
                (fun acc i => acc + if i = n + 1 then a else 0) 0 = 0 := by
          apply fold_add_zero_terms
          intro i hi
          have hi' : i < n + 1 := List.mem_range.mp hi
          have hne : i ≠ n + 1 := by omega
          rw [if_neg hne]
        rw [hzero]
        rw [if_pos rfl]
        exact zmod_zero_add a
      · have ht' : t < n + 1 := by omega
        rw [ih ht']
        have hne : n + 1 ≠ t := by omega
        rw [if_neg hne]
        exact zmod_add_zero a

private theorem fold_add_single_range_zero
    (n t : Nat) (a : ZMod64 p) (ht : ¬ t < n + 1) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + if i = t then a else 0) 0 = 0 := by
  apply fold_add_zero_terms
  intro i hi
  have hi' : i < n + 1 := List.mem_range.mp hi
  have hit : i ≠ t := by omega
  simp [hit]

theorem coeff_mul_shift_scale_one
    (f : FpPoly p) (c : ZMod64 p) (i n : Nat) :
    (f * DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))).coeff n =
      if i ≤ n then f.coeff (n - i) * c else 0 := by
  rw [coeff_mul, mulCoeffSum_eq_degree_bound f
    (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n]
  by_cases hin : i ≤ n
  · calc
      (List.range (n + 1)).foldl
          (fun acc j =>
            acc + mulCoeffTerm f
              (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n j) 0
          =
        (List.range (n + 1)).foldl
          (fun acc j => acc + if j = n - i then f.coeff (n - i) * c else 0) 0 := by
            apply fold_add_congr
            intro j hj
            have hjn : j < n + 1 := List.mem_range.mp hj
            unfold mulCoeffTerm
            by_cases hnj : n < j
            · have hne : j ≠ n - i := by omega
              rw [if_pos hnj, if_neg hne]
            · simp [hnj]
              have hzero : c * (0 : ZMod64 p) = 0 := by grind
              rw [DensePoly.coeff_shift_scale i c (1 : FpPoly p) (n - j) hzero]
              by_cases hlt : n - j < i
              · have hne : j ≠ n - i := by
                  intro hji
                  subst j
                  have hnot : ¬ n - (n - i) < i := by
                    rw [Nat.sub_sub_self hin]
                    omega
                  exact hnot hlt
                rw [if_neg hne]
                simp [hlt]
                exact zmod_mul_zero (f.coeff j)
              · by_cases hji : j = n - i
                · subst j
                  rw [if_pos rfl]
                  simp [hlt]
                  rw [coeff_one]
                  have hsub : n - (n - i) - i = 0 := by
                    rw [Nat.sub_sub_self hin]
                    simp
                  simp [hsub]
                  grind
                · rw [if_neg hji]
                  simp [hlt]
                  rw [coeff_one]
                  have hsub : n - j - i ≠ 0 := by omega
                  simp [hsub]
                  exact zmod_mul_zero (f.coeff j)
      _ = f.coeff (n - i) * c := by
            exact fold_add_single_range n (n - i) (f.coeff (n - i) * c) (by omega)
      _ = if i ≤ n then f.coeff (n - i) * c else 0 := by
            rw [if_pos hin]
  · have hzero :
        (List.range (n + 1)).foldl
            (fun acc j =>
              acc + mulCoeffTerm f
                (DensePoly.shift i (DensePoly.scale c (1 : FpPoly p))) n j) 0 = 0 := by
      apply fold_add_zero_terms
      intro j hj
      have hjn : j < n + 1 := List.mem_range.mp hj
      unfold mulCoeffTerm
      by_cases hnj : n < j
      · simp [hnj]
      · simp [hnj]
        have hzero : c * (0 : ZMod64 p) = 0 := by grind
        rw [DensePoly.coeff_shift_scale i c (1 : FpPoly p) (n - j) hzero]
        have hlt : n - j < i := by omega
        simp [hlt]
        exact zmod_mul_zero (f.coeff j)
    rw [hzero]
    rw [if_neg hin]

private theorem fold_mulCoeff_assoc_left_expand
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm (f * g) h n i) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 := by
  apply fold_add_congr
  intro i hi
  exact mulCoeffTerm_mul_left_expand f g h n i (by
    have hi' : i < n + 1 := List.mem_range.mp hi
    omega)

private theorem fold_mulCoeff_assoc_right_expand
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm f (g * h) n i) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
  apply fold_add_congr
  intro i hi
  exact mulCoeffTerm_mul_right_expand f g h n i (by
    have hi' : i < n + 1 := List.mem_range.mp hi
    omega)

private theorem fold_mulCoeff_assoc_left_normalize
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + (f.coeff j * g.coeff (i - j)) * h.coeff (n - i)) 0) 0 := by
  apply fold_add_congr
  intro i _hi
  apply fold_add_congr
  intro j hj
  have hji : ¬ i < j := by
    have hj' : j < i + 1 := List.mem_range.mp hj
    omega
  simp [mulCoeffTerm, hji]

private theorem fold_mulCoeff_assoc_right_normalize
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + (f.coeff i * g.coeff j) * h.coeff (n - i - j)) 0) 0 := by
  apply fold_add_congr
  intro i _hi
  apply fold_add_congr
  intro j hj
  have hji : ¬ n - i < j := by
    have hj' : j < n - i + 1 := List.mem_range.mp hj
    omega
  simp [mulCoeffTerm, hji]
  grind

private theorem mulCoeff_assoc_reindex
    (f g h : FpPoly p) (n : Nat) :
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 =
      (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
  calc
    (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (i + 1)).foldl
              (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0
        = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (i + 1)).foldl
                  (fun acc j => acc + (f.coeff j * g.coeff (i - j)) * h.coeff (n - i)) 0) 0 := by
            exact fold_mulCoeff_assoc_left_normalize f g h n
    _ = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (n - i + 1)).foldl
                  (fun acc j => acc + (f.coeff i * g.coeff j) * h.coeff (n - i - j)) 0) 0 := by
            exact fold_triangular_assoc_reindex n
              (fun a b c => (f.coeff a * g.coeff b) * h.coeff c)
    _ = (List.range (n + 1)).foldl
        (fun acc i =>
          acc +
            (List.range (n - i + 1)).foldl
              (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
            exact (fold_mulCoeff_assoc_right_normalize f g h n).symm

private theorem fold_left_distrib (xs : List Nat) (f g h : FpPoly p) (n : Nat) :
    xs.foldl (fun acc i => acc + mulCoeffTerm f (g + h) n i) 0 =
      xs.foldl (fun acc i => acc + mulCoeffTerm f g n i) 0 +
        xs.foldl (fun acc i => acc + mulCoeffTerm f h n i) 0 := by
  simpa [show (0 : ZMod64 p) + 0 = 0 by grind] using
    fold_distrib_acc (p := p) xs 0 0
      (fun i => mulCoeffTerm f (g + h) n i)
      (fun i => mulCoeffTerm f g n i)
      (fun i => mulCoeffTerm f h n i)
      (mulCoeffTerm_left_distrib f g h n)

private theorem fold_right_distrib (xs : List Nat) (f g h : FpPoly p) (n : Nat) :
    xs.foldl (fun acc i => acc + mulCoeffTerm (f + g) h n i) 0 =
      xs.foldl (fun acc i => acc + mulCoeffTerm f h n i) 0 +
        xs.foldl (fun acc i => acc + mulCoeffTerm g h n i) 0 := by
  simpa [show (0 : ZMod64 p) + 0 = 0 by grind] using
    fold_distrib_acc (p := p) xs 0 0
      (fun i => mulCoeffTerm (f + g) h n i)
      (fun i => mulCoeffTerm f h n i)
      (fun i => mulCoeffTerm g h n i)
      (mulCoeffTerm_right_distrib f g h n)

theorem left_distrib (f g h : FpPoly p) :
    f * (g + h) = f * g + f * h := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  simp [coeff_mul, mulCoeffSum, fold_left_distrib]

theorem right_distrib (f g h : FpPoly p) :
    (f + g) * h = f * h + g * h := by
  apply DensePoly.ext_coeff
  intro n
  let m := max (max (f + g).size f.size) g.size
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [coeff_mul_of_size_le (f + g) h n m (by dsimp [m]; omega)]
  rw [coeff_mul_of_size_le f h n m (by dsimp [m]; omega)]
  rw [coeff_mul_of_size_le g h n m (by dsimp [m]; omega)]
  exact fold_right_distrib (List.range m) f g h n

theorem mul_assoc (f g h : FpPoly p) :
    (f * g) * h = f * (g * h) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_degree_bound (f * g) h n]
  rw [mulCoeffSum_eq_degree_bound f (g * h) n]
  calc
    (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm (f * g) h n i) 0
        = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (i + 1)).foldl
                  (fun acc j => acc + mulCoeffTerm f g i j * h.coeff (n - i)) 0) 0 := by
            exact fold_mulCoeff_assoc_left_expand f g h n
    _ = (List.range (n + 1)).foldl
            (fun acc i =>
              acc +
                (List.range (n - i + 1)).foldl
                  (fun acc j => acc + f.coeff i * mulCoeffTerm g h (n - i) j) 0) 0 := by
            exact mulCoeff_assoc_reindex f g h n
    _ = (List.range (n + 1)).foldl
        (fun acc i => acc + mulCoeffTerm f (g * h) n i) 0 := by
            exact (fold_mulCoeff_assoc_right_expand f g h n).symm

theorem scale_add (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f + g) =
      DensePoly.scale c f + DensePoly.scale c g := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_add _ _ _ zmod_add_zero_zero]
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [DensePoly.coeff_scale _ _ _ hzero]
  grind

theorem scale_mul_left (c : ZMod64 p) (f g : FpPoly p) :
    DensePoly.scale c (f * g) =
      DensePoly.scale c f * g := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  rw [coeff_mul, coeff_mul]
  rw [mulCoeffSum_eq_degree_bound (DensePoly.scale c f) g n]
  rw [mulCoeffSum_eq_degree_bound f g n]
  rw [fold_mul_left]
  apply fold_add_congr
  intro i _hi
  unfold mulCoeffTerm
  by_cases hn : n < i
  · simp [hn]
    exact hzero
  · simp [hn]
    rw [DensePoly.coeff_scale _ _ _ hzero]
    grind
end FpPoly
end Hex
