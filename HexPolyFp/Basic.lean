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
      rw [DensePoly.coeff_add, DensePoly.coeff_shift_scale i (f.coeff i) g n hzero]
      rfl

theorem coeff_mul (f g : FpPoly p) (n : Nat) :
    (f * g).coeff n = mulCoeffSum f g n := by
  change (DensePoly.mul f g).coeff n = mulCoeffSum f g n
  unfold DensePoly.mul mulCoeffSum
  simpa [DensePoly.coeff_zero] using coeff_mul_fold (List.range f.size) 0 f g n

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
  · simp [hi, DensePoly.coeff_add]
    grind

private theorem mulCoeffTerm_right_distrib (f g h : FpPoly p) (n i : Nat) :
    mulCoeffTerm (f + g) h n i =
      mulCoeffTerm f h n i + mulCoeffTerm g h n i := by
  unfold mulCoeffTerm
  by_cases hi : n < i
  · simp [hi]
    grind
  · simp [hi, DensePoly.coeff_add]
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
  simp [DensePoly.coeff_add, coeff_mul, mulCoeffSum, fold_left_distrib]

theorem right_distrib (f g h : FpPoly p) :
    (f + g) * h = f * h + g * h := by
  apply DensePoly.ext_coeff
  intro n
  let m := max (max (f + g).size f.size) g.size
  rw [DensePoly.coeff_add]
  rw [coeff_mul_of_size_le (f + g) h n m (by dsimp [m]; omega)]
  rw [coeff_mul_of_size_le f h n m (by dsimp [m]; omega)]
  rw [coeff_mul_of_size_le g h n m (by dsimp [m]; omega)]
  exact fold_right_distrib (List.range m) f g h n

end FpPoly
end Hex
