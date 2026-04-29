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
