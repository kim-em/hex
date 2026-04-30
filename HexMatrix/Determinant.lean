import Std
import Init.Grind.Ring.Field
import Batteries.Data.Fin.Fold
import Batteries.Data.List.Lemmas
import Batteries.Data.Vector.Lemmas
import HexMatrix.RowEchelon

/-!
Determinant routines for `hex-matrix`.

This module adds the generic Leibniz-formula determinant for dense square
matrices together with the determinant behavior of the elementary row
operations used by row reduction and Bareiss pivot tracking.
-/

namespace Hex

universe u

namespace Matrix

variable {α : Type u}

/-- Insert an element into a vector at a given position. -/
def insertAt (x : α) (v : Vector α n) (i : Fin (n + 1)) : Vector α (n + 1) :=
  ⟨(v.toList.insertIdx i.val x).toArray, by
    have hi : i.val ≤ v.toList.length := by
      simpa using Nat.lt_succ_iff.mp i.isLt
    simpa using List.length_insertIdx_of_le_length (a := x) (as := v.toList) hi⟩

/-- The unique empty vector. -/
def emptyVec : Vector α 0 :=
  ⟨#[], rfl⟩

/-- Enumerate the permutations of `Fin n` as length-`n` vectors. -/
def permutationVectors : (n : Nat) → List (Vector (Fin n) n)
  | 0 => [emptyVec]
  | n + 1 =>
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n)

/-- Count inversions in a permutation written as a list. -/
def inversionCount : List (Fin n) → Nat
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 + inversionCount xs

private def crossInversionCount {n : Nat} : List (Fin n) → List (Fin n) → Nat
  | [], _ => 0
  | x :: xs, ys =>
      ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        crossInversionCount xs ys

private theorem foldCount_start {α : Type u} (xs : List α) (p : α → Prop)
    [DecidablePred p] (acc : Nat) :
    xs.foldl (fun acc y => acc + if p y then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if p y then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if p y then 1 else 0), ih (0 + if p y then 1 else 0)]
      omega

private theorem inversionFold_start {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if y < x then 1 else 0), ih (0 + if y < x then 1 else 0)]
      omega

private theorem inversionFold_append {n : Nat} (xs ys : List (Fin n)) (x : Fin n) :
    (xs ++ ys).foldl (fun acc y => acc + if y < x then 1 else 0) 0 =
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  rw [List.foldl_append, inversionFold_start]

private theorem inversionCount_append {n : Nat} (xs ys : List (Fin n)) :
    inversionCount (xs ++ ys) =
      inversionCount xs + inversionCount ys + crossInversionCount xs ys := by
  induction xs with
  | nil =>
      change inversionCount ys =
        inversionCount ([] : List (Fin n)) + inversionCount ys +
          crossInversionCount ([] : List (Fin n)) ys
      simp [inversionCount, crossInversionCount]
  | cons x xs ih =>
      simp only [List.cons_append, inversionCount, crossInversionCount]
      rw [inversionFold_append, ih]
      omega

private theorem crossInversionCount_append_left {n : Nat}
    (xs ys zs : List (Fin n)) :
    crossInversionCount (xs ++ ys) zs =
      crossInversionCount xs zs + crossInversionCount ys zs := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [List.cons_append, crossInversionCount]
      rw [ih]
      omega

private theorem crossInversionCount_append_right {n : Nat}
    (xs ys zs : List (Fin n)) :
    crossInversionCount xs (ys ++ zs) =
      crossInversionCount xs ys + crossInversionCount xs zs := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [crossInversionCount]
      rw [inversionFold_append, ih]
      omega

private theorem crossInversionCount_singleton_left {n : Nat}
    (x : Fin n) (ys : List (Fin n)) :
    crossInversionCount [x] ys =
      ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  simp [crossInversionCount]

private theorem crossInversionCount_singleton_right {n : Nat}
    (xs : List (Fin n)) (y : Fin n) :
    crossInversionCount xs [y] =
      xs.foldl (fun acc x => acc + if y < x then 1 else 0) 0 := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp only [crossInversionCount, List.foldl_cons, List.foldl_nil]
      rw [ih]
      exact (foldCount_start xs (fun x => y < x) (0 + if y < x then 1 else 0)).symm

private theorem crossInversionCount_pair_swap_right {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    crossInversionCount xs [a, b] =
      crossInversionCount xs [b, a] := by
  induction xs with
  | nil =>
      simp [crossInversionCount]
  | cons x xs ih =>
      simp [crossInversionCount]
      rw [ih]
      omega

private theorem crossInversionCount_pair_swap_left {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    crossInversionCount [a, b] xs =
      crossInversionCount [b, a] xs := by
  simp [crossInversionCount]
  omega

private theorem inversionCount_pair {n : Nat} (a b : Fin n) :
    inversionCount [a, b] = if b < a then 1 else 0 := by
  simp [inversionCount]

private theorem inversionCount_adjacent_swap_parity {n : Nat}
    (pre post : List (Fin n)) (a b : Fin n) (h : a ≠ b) :
    inversionCount (pre ++ a :: b :: post) % 2 =
      (inversionCount (pre ++ b :: a :: post) + 1) % 2 := by
  have horder : a < b ∨ b < a := by
    have hval : a.val ≠ b.val := by
      intro hv
      exact h (Fin.ext hv)
    cases Nat.lt_or_gt_of_ne hval with
    | inl hab => exact Or.inl hab
    | inr hba => exact Or.inr hba
  rw [show pre ++ a :: b :: post = pre ++ ([a, b] ++ post) by simp]
  rw [show pre ++ b :: a :: post = pre ++ ([b, a] ++ post) by simp]
  have hcross :
      crossInversionCount pre ([a, b] ++ post) =
        crossInversionCount pre ([b, a] ++ post) := by
    repeat rw [crossInversionCount_append_right]
    rw [crossInversionCount_pair_swap_right]
  have htail :
      crossInversionCount [a, b] post =
        crossInversionCount [b, a] post := by
    exact crossInversionCount_pair_swap_left post a b
  rw [inversionCount_append pre ([a, b] ++ post)]
  rw [inversionCount_append pre ([b, a] ++ post)]
  rw [hcross]
  rw [inversionCount_append [a, b] post]
  rw [inversionCount_append [b, a] post]
  rw [htail]
  rw [inversionCount_pair a b]
  rw [inversionCount_pair b a]
  cases horder with
  | inl hab =>
      have hba : ¬ b < a := by omega
      simp [hab, hba]
      omega
  | inr hba =>
      have hab : ¬ a < b := by omega
      simp [hab, hba]
      omega

private theorem inversionCount_swap_separated_parity {n : Nat}
    (pre mid post : List (Fin n)) (a b : Fin n)
    (hnodup : (pre ++ a :: mid ++ b :: post).Nodup) :
    inversionCount (pre ++ b :: mid ++ a :: post) % 2 =
      (inversionCount (pre ++ a :: mid ++ b :: post) + 1) % 2 := by
  induction mid generalizing pre with
  | nil =>
      have hne : b ≠ a := by
        intro hba
        subst b
        have hsplit : ((pre ++ [a]) ++ a :: post).Nodup := by
          simpa [List.append_assoc] using hnodup
        exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: post)).mp hsplit).2.2
          a (by simp) a (by simp) rfl
      simpa [Nat.add_comm] using
        (inversionCount_adjacent_swap_parity pre post b a hne)
  | cons x xs ih =>
      have hswap₁ :
          inversionCount (pre ++ b :: x :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: b :: xs ++ a :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          inversionCount_adjacent_swap_parity pre (xs ++ a :: post) b x (by
            intro hbx
            subst b
            have hsplit : ((pre ++ a :: x :: xs) ++ x :: post).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ a :: x :: xs) (l₂ := x :: post)).mp hsplit).2.2
              x (by simp) x (by simp) rfl)
      have hnodup_tail : ((pre ++ [x]) ++ a :: xs ++ b :: post).Nodup := by
        have hp :
            ((pre ++ [x]) ++ a :: xs ++ b :: post).Perm
              (pre ++ a :: x :: xs ++ b :: post) := by
          simpa [List.append_assoc] using
            List.Perm.append_left pre (List.Perm.swap a x (xs ++ b :: post))
        exact hp.nodup_iff.mpr hnodup
      have hmid :
          inversionCount (pre ++ x :: b :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: a :: xs ++ b :: post) + 1) % 2 := by
        simpa only [List.cons_append, List.append_assoc] using
          (ih (pre ++ [x]) hnodup_tail)
      have hswap₂ :
          inversionCount (pre ++ x :: a :: xs ++ b :: post) % 2 =
            (inversionCount (pre ++ a :: x :: xs ++ b :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          inversionCount_adjacent_swap_parity pre (xs ++ b :: post) x a (by
            intro hxa
            subst x
            have hsplit : (pre ++ [a] ++ (a :: xs ++ b :: post)).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: xs ++ b :: post)).mp hsplit).2.2
              a (by simp) a (by simp) rfl)
      omega

/-- The sign of a permutation vector, computed from inversion parity. -/
def detSign {R : Type u} [Lean.Grind.Ring R] {n : Nat} (perm : Vector (Fin n) n) : R :=
  if inversionCount perm.toList % 2 = 0 then 1 else -1

/-- The unsigned product associated to a permutation vector. -/
def detProduct {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * M[i][perm[i]]) 1

/-- The Leibniz summand associated to a permutation vector. -/
def detTerm {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  detSign perm * detProduct M perm

/-- The determinant of a dense square matrix, defined by the Leibniz formula. -/
def det {R : Type u} [Lean.Grind.Ring R] {n : Nat} (M : Matrix R n n) : R :=
  (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0

/-- Congruence for the determinant-style left fold over a finite list. -/
private theorem foldl_det_sum_congr {R : Type u} [Add R] {β : Type v}
    (xs : List β) (f g : β → R) (z : R)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldl (fun acc x => acc + f x) z =
      xs.foldl (fun acc x => acc + g x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

private theorem foldl_det_product_congr {R : Type u} [Mul R] {β : Type v}
    (xs : List β) (f g : β → R) (z : R)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldl (fun acc x => acc * f x) z =
      xs.foldl (fun acc x => acc * g x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

/-- Factor a scalar out of a determinant-style finite left fold. -/
private theorem foldl_det_sum_mul_left {R : Type u} [Lean.Grind.CommRing R] {β : Type v}
    (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc + c * f x) (c * z) =
      c * xs.foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z + f x) = c * z + c * f x by grind]
      exact ih (z + f x)

/-- Factor a scalar out of a determinant-style finite left fold from zero. -/
private theorem foldl_det_sum_mul_left_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) :
    xs.foldl (fun acc x => acc + c * f x) 0 =
      c * xs.foldl (fun acc x => acc + f x) 0 := by
  have hzero : c * 0 = 0 := by grind
  simpa [hzero] using (foldl_det_sum_mul_left (R := R) xs c f 0)

private theorem foldl_det_sum_add_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f g : β → R) (a b : R) :
    xs.foldl (fun acc x => acc + (f x + g x)) (a + b) =
      xs.foldl (fun acc x => acc + f x) a +
        xs.foldl (fun acc x => acc + g x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun acc x => acc + (f x + g x)) (a + b + (f x + g x)) =
          xs.foldl (fun acc x => acc + (f x + g x)) ((a + f x) + (b + g x)) := by
            congr 1
            grind
        _ =
          xs.foldl (fun acc x => acc + f x) (a + f x) +
            xs.foldl (fun acc x => acc + g x) (b + g x) := by
            exact ih (a + f x) (b + g x)

private theorem foldl_det_sum_add_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f g : β → R) :
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + f x) 0 +
        xs.foldl (fun acc x => acc + g x) 0 := by
  calc
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + (f x + g x)) ((0 : R) + 0) := by
        congr 1
        grind
    _ =
      xs.foldl (fun acc x => acc + f x) 0 +
        xs.foldl (fun acc x => acc + g x) 0 := by
        exact foldl_det_sum_add_start xs f g 0 0

private theorem foldl_det_sum_flatMap {R : Type u} [Add R] {β γ : Type v}
    (xs : List β) (f : β → List γ) (g : γ → R) (z : R) :
    (xs.flatMap f).foldl (fun acc x => acc + g x) z =
      xs.foldl (fun acc x => (f x).foldl (fun acc y => acc + g y) acc) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons]
      exact ih ((f x).foldl (fun acc y => acc + g y) z)

private theorem foldl_det_sum_zero {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (z : R) :
    xs.foldl (fun acc _ => acc + 0) z = z := by
  induction xs generalizing z with
  | nil => rfl
  | cons _ xs ih =>
      simp only [List.foldl_cons]
      have hzero : z + (0 : R) = z := by grind
      simpa [hzero] using ih z

private theorem foldl_det_product_mul_left {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (c : R) (f : β → R) (z : R) :
    xs.foldl (fun acc x => acc * f x) (c * z) =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← show c * (z * f x) = (c * z) * f x by grind]
      exact ih (z * f x)

private theorem foldl_det_product_no_scale_of_not_mem {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R) (hnot : i ∉ xs) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mem_cons, not_or] at hnot
      simp only [List.foldl_cons]
      have hx : x ≠ i := by
        intro hxi
        exact hnot.1 hxi.symm
      rw [if_neg hx]
      exact ih (z * f x) hnot.2

private theorem foldl_det_product_single_scale {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup) :
    xs.foldl (fun acc x => acc * if x = i then c * f x else f x) z =
      c * xs.foldl (fun acc x => acc * f x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        calc
          xs.foldl (fun acc x => acc * if x = i then c * f x else f x) (z * (c * f i)) =
              xs.foldl (fun acc x => acc * f x) (z * (c * f i)) := by
                exact foldl_det_product_no_scale_of_not_mem xs i c f (z * (c * f i)) hnodup.1
          _ = xs.foldl (fun acc x => acc * f x) (c * (z * f i)) := by
                congr 1
                grind
          _ = c * xs.foldl (fun acc x => acc * f x) (z * f i) := by
                exact foldl_det_product_mul_left xs c f (z * f i)
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) hmemTail hnodup.2

private theorem foldl_det_product_add_start {R : Type u} [Lean.Grind.CommRing R]
    {β : Type v} (xs : List β) (f : β → R) (a b : R) :
    xs.foldl (fun acc x => acc * f x) (a + b) =
      xs.foldl (fun acc x => acc * f x) a +
        xs.foldl (fun acc x => acc * f x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        xs.foldl (fun acc x => acc * f x) ((a + b) * f x) =
          xs.foldl (fun acc x => acc * f x) (a * f x + b * f x) := by
            congr 1
            grind
        _ =
          xs.foldl (fun acc x => acc * f x) (a * f x) +
            xs.foldl (fun acc x => acc * f x) (b * f x) := by
            exact ih (a * f x) (b * f x)

private theorem foldl_det_product_single_add {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (c : R) (f g : β → R) (z : R)
    (hmem : i ∈ xs) (hnodup : xs.Nodup)
    (hagree : ∀ x, x ∈ xs → x ≠ i → g x = f x) :
    xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x) z =
      xs.foldl (fun acc x => acc * f x) z +
        c * xs.foldl (fun acc x => acc * g x) z := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [if_pos rfl]
        have hnot : i ∉ xs := hnodup.1
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * (f i + c * g i)) =
            xs.foldl (fun acc x => acc * f x) (z * (f i + c * g i)) := by
              apply foldl_det_product_congr
              intro y hy
              have hyi : y ≠ i := by
                intro h
                exact hnot (h ▸ hy)
              rw [if_neg hyi]
          _ = xs.foldl (fun acc x => acc * f x) (z * f i + c * (z * g i)) := by
              congr 1
              grind
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              xs.foldl (fun acc x => acc * f x) (c * (z * g i)) := by
              exact foldl_det_product_add_start xs f (z * f i) (c * (z * g i))
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * f x) (z * g i) := by
              rw [show
                xs.foldl (fun acc x => acc * f x) (c * (z * g i)) =
                  c * xs.foldl (fun acc x => acc * f x) (z * g i) from
                    foldl_det_product_mul_left xs c f (z * g i)]
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f i) +
              c * xs.foldl (fun acc x => acc * g x) (z * g i) := by
              congr 2
              apply foldl_det_product_congr
              intro y hy
              exact (hagree y (List.mem_cons.mpr (Or.inr hy)) (by
                intro h
                exact hnot (h ▸ hy))).symm
      · rw [if_neg hx]
        have hmemTail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        have hgx : g x = f x := hagree x (List.mem_cons.mpr (Or.inl rfl)) hx
        calc
          xs.foldl (fun acc x => acc * if x = i then f x + c * g x else f x)
              (z * f x) =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * f x) := by
              exact ih (z * f x) hmemTail hnodup.2
                (fun y hy hyi => hagree y (List.mem_cons.mpr (Or.inr hy)) hyi)
          _ =
            xs.foldl (fun acc x => acc * f x) (z * f x) +
              c * xs.foldl (fun acc x => acc * g x) (z * g x) := by
              rw [hgx]

private theorem foldl_det_product_zero_start {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} (xs : List β) (f : β → R) :
    xs.foldl (fun acc x => acc * f x) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hzero : (0 : R) * f x = 0 := by grind
      simpa [hzero] using ih

private theorem foldl_det_product_zero_of_mem {R : Type u}
    [Lean.Grind.CommRing R] {β : Type v} [DecidableEq β]
    (xs : List β) (i : β) (f : β → R) (z : R)
    (hmem : i ∈ xs) (hzero : f i = 0) :
    xs.foldl (fun acc x => acc * f x) z = 0 := by
  induction xs generalizing z with
  | nil =>
      cases hmem
  | cons x xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldl_cons]
      by_cases hx : x = i
      · subst x
        rw [hzero]
        have hz : z * (0 : R) = 0 := by grind
        simpa [hz] using foldl_det_product_zero_start xs f
      · have htail : i ∈ xs := by
          cases hmem with
          | inl hxi => exact False.elim (hx hxi.symm)
          | inr htail => exact htail
        exact ih (z * f x) htail

private theorem identity_get {R : Type u} [OfNat R 0] [OfNat R 1] {n : Nat}
    (i j : Fin n) :
    (1 : Matrix R n n)[i][j] = if i = j then 1 else 0 := by
  change Matrix.identity[i][j] = if i = j then 1 else 0
  simp [Matrix.identity, Matrix.ofFn]

private theorem detProduct_identity_zero_of_mismatch {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (perm : Vector (Fin n) n)
    (i : Fin n) (h : perm[i] ≠ i) :
    detProduct (1 : Matrix R n n) perm = 0 := by
  unfold detProduct
  have hsymm : i ≠ perm[i] := by
    intro hi
    exact h hi.symm
  exact foldl_det_product_zero_of_mem
    (List.finRange n) i (fun r => (1 : Matrix R n n)[r][perm[r]]) 1
    (List.mem_finRange i) (by
      change (1 : Matrix R n n)[i][perm[i]] = 0
      rw [identity_get]
      rw [if_neg hsymm])

private theorem insertAt_get_self {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) :
    (insertAt x v i)[i] = x := by
  unfold insertAt
  simp [List.getElem_insertIdx_self]

private theorem insertAt_last_get_castSucc {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin n) :
    (insertAt x v (Fin.last n))[i.castSucc] = v[i] := by
  unfold insertAt
  simp [List.getElem_insertIdx_of_lt]

private theorem detProduct_identity_insertAt_not_last_zero {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n)
    (i : Fin (n + 1)) (h : i ≠ Fin.last n) :
    detProduct (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) i) = 0 := by
  apply detProduct_identity_zero_of_mismatch
  exact by
    rw [insertAt_get_self]
    exact h.symm

private theorem detProduct_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detProduct (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detProduct (1 : Matrix R n n) v := by
  unfold detProduct
  rw [← Fin.foldl_eq_foldl_finRange, ← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hfold :
      Fin.foldl n
          (fun acc i =>
            acc *
              (1 : Matrix R (n + 1) (n + 1))[i.castSucc][
                (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc]]) 1 =
      Fin.foldl n (fun acc i => acc * (1 : Matrix R n n)[i][v[i]]) 1 := by
    congr
    funext acc i
    rw [identity_get, identity_get]
    have hget :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[i.castSucc] =
          (v[i]).castSucc := by
      simpa using insertAt_last_get_castSucc (Fin.last n) (v.map Fin.castSucc) i
    rw [hget]
    simp [Fin.ext_iff]
  have hlast :
      (1 : Matrix R (n + 1) (n + 1))[Fin.last n][
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n]] = 1 := by
    rw [identity_get]
    have hself :
        (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n))[Fin.last n] =
          Fin.last n := by
      exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) (Fin.last n)
    simp [hself]
  rw [hfold, hlast]
  have hmul_one : ∀ x : R, x * (1 : R) = x := by
    intro x
    exact Lean.Grind.Semiring.mul_one x
  exact hmul_one _

private theorem inversionFold_map_castSucc {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if y.castSucc < x.castSucc then 1 else 0) =
            (if y < x then 1 else 0) := by
        simp [Fin.lt_def]
      rw [hhead]
      exact ih _

private theorem inversionCount_map_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount (xs.map Fin.castSucc) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inversionCount, ih, inversionFold_map_castSucc]

private theorem inversionCount_insert_last_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount ((xs.map Fin.castSucc) ++ [Fin.last n]) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.cons_append, inversionCount]
      rw [ih]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [inversionFold_map_castSucc]
      simp [Fin.lt_def]

private theorem list_insertIdx_length {α : Type u} (xs : List α) (x : α) :
    xs.insertIdx xs.length x = xs ++ [x] := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp [ih]

private theorem vector_toList_map {α β : Type u} {n : Nat} (v : Vector α n)
    (f : α → β) :
    (v.map f).toList = v.toList.map f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

private theorem insertAt_last_toList {α : Type u} {n : Nat} (x : α) (v : Vector α n) :
    (insertAt x v (Fin.last n)).toList = v.toList ++ [x] := by
  unfold insertAt
  simp only [Vector.toList]
  have hidx : (Fin.last n).val = v.toArray.toList.length := by
    simp
  simpa [hidx] using list_insertIdx_length v.toArray.toList x

private theorem insertAt_toList {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) :
    (insertAt x v i).toList = v.toList.insertIdx i.val x := by
  unfold insertAt
  simp [Vector.toList]

private theorem list_nodup_map_castSucc {n : Nat} (xs : List (Fin n)) :
    xs.Nodup → (xs.map Fin.castSucc).Nodup := by
  induction xs with
  | nil =>
      intro _h
      simp
  | cons x xs ih =>
      intro hnodup
      rw [List.nodup_cons] at hnodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hxy⟩
        have hval : x.val = y.val := by
          simpa using (congrArg Fin.val hxy).symm
        exact hnodup.1 (Fin.ext hval ▸ hy)
      · exact ih hnodup.2

private theorem finLast_not_mem_map_castSucc {n : Nat} (xs : List (Fin n)) :
    Fin.last n ∉ xs.map Fin.castSucc := by
  intro hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨x, _hxmem, hxlast⟩
  have hval : x.val = n := by
    simpa using congrArg Fin.val hxlast
  exact Nat.ne_of_lt x.isLt hval

private theorem insertAt_last_castSucc_nodup {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1))
    (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup := by
  rw [insertAt_toList]
  have hmap : (v.map Fin.castSucc).toList.Nodup := by
    rw [vector_toList_map]
    exact list_nodup_map_castSucc v.toList hnodup
  have hlast : Fin.last n ∉ (v.map Fin.castSucc).toList := by
    rw [vector_toList_map]
    exact finLast_not_mem_map_castSucc v.toList
  have hcons : (Fin.last n :: (v.map Fin.castSucc).toList).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hlast, hmap⟩
  have hidx : i.val ≤ (v.map Fin.castSucc).toList.length := by
    simpa using Nat.lt_succ_iff.mp i.isLt
  exact (List.perm_insertIdx (Fin.last n) (v.map Fin.castSucc).toList hidx).symm.nodup hcons

private theorem finList_length_le_card {n : Nat} {xs : List (Fin n)}
    (hnodup : xs.Nodup) :
    xs.length ≤ n := by
  have hsub : List.Subperm xs (List.finRange n) := by
    exact List.subperm_of_subset hnodup (fun x _hx => List.mem_finRange x)
  simpa [List.length_finRange] using List.Subperm.length_le hsub

private theorem finLast_mem_of_full_nodup {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    Fin.last n ∈ xs := by
  by_cases hmem : Fin.last n ∈ xs
  · exact hmem
  · exfalso
    have hsub : List.Subperm xs ((List.finRange (n + 1)).erase (Fin.last n)) := by
      apply List.subperm_of_subset hnodup
      intro x hx
      exact (List.mem_erase_of_ne (by
        intro hxlast
        exact hmem (hxlast ▸ hx))).2 (List.mem_finRange x)
    have hle : xs.length ≤ ((List.finRange (n + 1)).erase (Fin.last n)).length :=
      List.Subperm.length_le hsub
    have herase :
        ((List.finRange (n + 1)).erase (Fin.last n)).length = n := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    omega

private def lowerFinLast {n : Nat} (x : Fin (n + 1)) (h : x ≠ Fin.last n) :
    Fin n :=
  ⟨x.val, by
    have hxlt : x.val < n + 1 := x.isLt
    have hxne : x.val ≠ n := by
      intro hx
      exact h (Fin.ext hx)
    omega⟩

private theorem lowerFinLast_castSucc {n : Nat} (x : Fin (n + 1))
    (h : x ≠ Fin.last n) :
    (lowerFinLast x h).castSucc = x := by
  exact Fin.ext rfl

private theorem finLast_idxOf_lt_of_full_nodup {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    xs.idxOf (Fin.last n) < xs.length := by
  exact List.idxOf_lt_length_of_mem (finLast_mem_of_full_nodup hlen hnodup)

private def peelLastVector {n : Nat} (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (_hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) : Vector (Fin n) n :=
  Vector.ofFn fun r =>
    let j := if r.val < k then r.val else r.val + 1
    have hj : j < n + 1 := by
      dsimp [j]
      split
      · omega
      · have hr : r.val < n := r.isLt
        omega
    let y := perm[(⟨j, hj⟩ : Fin (n + 1))]
    lowerFinLast y (by
      intro hy
      have hjlen : j < perm.toList.length := by
        simpa [Vector.length_toList] using hj
      have hjidx :
          perm.toList.idxOf (perm.toList[j]'hjlen) = j := by
        exact hnodup.idxOf_getElem j hjlen
      have hylist : perm.toList[j]'hjlen = Fin.last n := by
        simpa [Vector.getElem_toList] using hy
      have hkj : k = j := by
        rw [← hidx, ← hylist, hjidx]
      dsimp [j] at hkj
      split at hkj
      · omega
      · omega)

private theorem peelLastVector_castSucc_toList {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc).toList =
      perm.toList.eraseIdx k := by
  sorry

private theorem peelLastVector_nodup {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    (peelLastVector perm k hk hidx hnodup).toList.Nodup := by
  sorry

private theorem insertAt_peelLastVector {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    insertAt (Fin.last n)
        ((peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩ =
      perm := by
  sorry

private theorem permutationVectors_complete {n : Nat} {perm : Vector (Fin n) n}
    (hnodup : perm.toList.Nodup) :
    perm ∈ permutationVectors n := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      have hperm : perm = emptyVec := by
        apply Vector.ext
        intro i hi
        omega
      simp [permutationVectors, hperm]
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          finLast_idxOf_lt_of_full_nodup (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := peelLastVector perm k hk hidx hnodup
      have hpeeled : peeled ∈ permutationVectors n := by
        exact ih (peelLastVector_nodup perm k hk hidx hnodup)
      change perm ∈
        List.flatMap
          (fun v =>
            (List.finRange (n + 1)).map fun i =>
              insertAt (Fin.last n) (v.map Fin.castSucc) i)
          (permutationVectors n)
      rw [List.mem_flatMap]
      refine ⟨peeled, hpeeled, ?_⟩
      rw [List.mem_map]
      refine ⟨(⟨k, hk⟩ : Fin (n + 1)), List.mem_finRange (⟨k, hk⟩ : Fin (n + 1)), ?_⟩
      exact insertAt_peelLastVector perm k hk hidx hnodup

private theorem permutationVectors_nodup {n : Nat} {perm : Vector (Fin n) n}
    (hmem : perm ∈ permutationVectors n) :
    perm.toList.Nodup := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      rw [hnil]
      simp
  | succ n ih =>
      simp [permutationVectors, List.mem_flatMap, List.mem_map] at hmem
      rcases hmem with ⟨v, hv, i, _hi, rfl⟩
      exact insertAt_last_castSucc_nodup v i (ih hv)

private theorem detSign_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (v : Vector (Fin n) n) :
    detSign (R := R)
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detSign (R := R) v := by
  unfold detSign
  rw [insertAt_last_toList, vector_toList_map, inversionCount_insert_last_castSucc]

private theorem detTerm_identity_insertAt_last {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) :
    detTerm (1 : Matrix R (n + 1) (n + 1))
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detTerm (1 : Matrix R n n) v := by
  unfold detTerm
  rw [detSign_insertAt_last, detProduct_identity_insertAt_last]

private theorem foldl_detTerm_identity_insertions {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat} (v : Vector (Fin n) n) (z : R) :
    (List.finRange (n + 1)).foldl
        (fun acc i =>
          acc + detTerm (1 : Matrix R (n + 1) (n + 1))
            (insertAt (Fin.last n) (v.map Fin.castSucc) i)) z =
      z + detTerm (1 : Matrix R n n) v := by
  rw [← Fin.foldl_eq_foldl_finRange]
  rw [Fin.foldl_succ_last]
  have hprefix :
      Fin.foldl n
          (fun acc i =>
            acc + detTerm (1 : Matrix R (n + 1) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z = z := by
    rw [Fin.foldl_eq_foldl_finRange]
    calc
      (List.finRange n).foldl
          (fun acc i =>
            acc + detTerm (1 : Matrix R (n + 1) (n + 1))
              (insertAt (Fin.last n) (v.map Fin.castSucc) i.castSucc)) z =
        (List.finRange n).foldl (fun acc (_i : Fin n) => acc + (0 : R)) z := by
          apply foldl_det_sum_congr
          intro i _hmem
          unfold detTerm
          rw [detProduct_identity_insertAt_not_last_zero (R := R) v i.castSucc (by
            intro hlast
            have hval := congrArg Fin.val hlast
            simp at hval
            exact (Nat.ne_of_lt i.isLt) hval)]
          grind
      _ = z := by
          exact foldl_det_sum_zero (List.finRange n) z
  rw [hprefix]
  rw [detTerm_identity_insertAt_last]

private theorem rowScale_get {R : Type u} [Mul R] {n m : Nat}
    (M : Matrix R n m) (i r : Fin n) (c : R) (k : Fin m) :
    (rowScale M i c)[r][k] = if r = i then c * M[i][k] else M[r][k] := by
  by_cases h : r = i
  · subst r
    simp [rowScale]
  · simp [rowScale, h]
    have hval : i.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set i (Vector.ofFn fun k => c * M[i][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne (xs := M) (x := Vector.ofFn fun k => c * M[i][k])
          i.isLt r.isLt hval)
    simpa [rowScale] using congrArg (fun row => row[k]) hrow

private theorem detProduct_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowScale M i c) perm = c * detProduct M perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowScale M i c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r => acc * if r = i then c * M[r][perm[r]] else M[r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        by_cases h : r = i
        · subst r
          simpa using (rowScale_get M i i c perm[i])
        · simpa [h] using (rowScale_get M i r c perm[r])
    _ = c * (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 := by
        exact foldl_det_product_single_scale
          (List.finRange n) i c (fun r => M[r][perm[r]]) 1
          (List.mem_finRange i) (List.nodup_finRange n)

private def finTranspose {n : Nat} (i j : Fin n) (r : Fin n) : Fin n :=
  if r = i then j else if r = j then i else r

private theorem finTranspose_left {n : Nat} (i j : Fin n) :
    finTranspose i j i = j := by
  simp [finTranspose]

private theorem finTranspose_right {n : Nat} (i j : Fin n) :
    finTranspose i j j = i := by
  by_cases h : j = i
  · subst j
    simp [finTranspose]
  · simp [finTranspose, h]

private theorem finTranspose_of_ne {n : Nat} (i j r : Fin n)
    (hi : r ≠ i) (hj : r ≠ j) :
    finTranspose i j r = r := by
  simp [finTranspose, hi, hj]

private theorem finTranspose_involutive {n : Nat} (i j r : Fin n) :
    finTranspose i j (finTranspose i j r) = r := by
  by_cases hi : r = i
  · subst r
    rw [finTranspose_left, finTranspose_right]
  · by_cases hj : r = j
    · subst r
      rw [finTranspose_right, finTranspose_left]
    · rw [finTranspose_of_ne i j r hi hj]
      exact finTranspose_of_ne i j r hi hj

private theorem finTranspose_injective {n : Nat} (i j : Fin n) :
    Function.Injective (finTranspose i j) := by
  intro a b h
  have h' := congrArg (finTranspose i j) h
  simpa [finTranspose_involutive] using h'

private theorem finTranspose_ne_iff {n : Nat} (i j a b : Fin n) :
    finTranspose i j a ≠ finTranspose i j b ↔ a ≠ b := by
  constructor
  · intro h hab
    exact h (hab ▸ rfl)
  · intro h hab
    exact h (finTranspose_injective i j hab)

private def transposePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  Vector.ofFn fun r => perm[finTranspose i j r]

private theorem rowSwap_get {R : Type u} {n m : Nat}
    (M : Matrix R n m) (i j r : Fin n) (k : Fin m) :
    (rowSwap M i j)[r][k] =
      if r = j then M[i][k] else if r = i then M[j][k] else M[r][k] := by
  by_cases hrj : r = j
  · subst r
    simp [rowSwap]
  · by_cases hri : r = i
    · subst r
      simp [rowSwap, hrj]
      have hval : j.val ≠ i.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow : ((M.set i M[j]).set j M[i])[i] = (M.set i M[j])[i] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i]) j.isLt i.isLt hval
      simpa using congrArg (fun row => row[k]) hrow
    · simp [rowSwap, hrj, hri]
      have hir : i.val ≠ r.val := by
        intro hval
        exact hri (Fin.ext hval.symm)
      have hjr : j.val ≠ r.val := by
        intro hval
        exact hrj (Fin.ext hval.symm)
      have hrow₁ : (M.set i M[j])[r] = M[r] := by
        exact Vector.getElem_set_ne (xs := M) (x := M[j]) i.isLt r.isLt hir
      have hrow₂ : ((M.set i M[j]).set j M[i])[r] = (M.set i M[j])[r] := by
        exact Vector.getElem_set_ne (xs := M.set i M[j]) (x := M[i]) j.isLt r.isLt hjr
      exact (congrArg (fun row => row[k]) hrow₂).trans (congrArg (fun row => row[k]) hrow₁)

private theorem transposePermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (transposePermutationValues perm i j)[r] = perm[finTranspose i j r] := by
  simp [transposePermutationValues]

private theorem vector_get_fin_congr {α : Type u} {n : Nat} (v : Vector α n)
    {a b : Fin n} (h : a = b) : v[a] = v[b] := by
  subst b
  rfl

private theorem vector_toList_split_two {α : Type u} {n : Nat}
    (v : Vector α n) {i j : Fin n} (hij : i.val < j.val) :
    v.toList =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
  have hi : i.val < v.toList.length := by
    simp [Vector.length_toList]
  have hjdrop : j.val - i.val - 1 < (v.toList.drop (i.val + 1)).length := by
    simp only [List.length_drop, Vector.length_toList]
    omega
  calc
    v.toList = v.toList.take i.val ++ v.toList.drop i.val := by
      exact (List.take_append_drop i.val v.toList).symm
    _ = v.toList.take i.val ++ v[i] :: v.toList.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      simp [Vector.getElem_toList]
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          (v.toList.drop (i.val + 1)).drop (j.val - i.val - 1) := by
      rw [List.append_assoc]
      congr 1
      congr 1
      exact (List.take_append_drop (j.val - i.val - 1)
        (v.toList.drop (i.val + 1))).symm
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
      have hmid : i.val + 1 + (j.val - i.val - 1) = j.val := by
        omega
      have hdrop : i.val + 1 + ((j.val - i.val - 1) + 1) = j.val + 1 := by
        omega
      rw [List.drop_eq_getElem_cons hjdrop]
      simp [List.drop_drop, Vector.getElem_toList, List.getElem_drop, hmid, hdrop]

private theorem transposePermutationValues_take_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList.take i.val =
      perm.toList.take i.val := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hk : k < n := by omega
    have hki : (⟨k, hk⟩ : Fin n) ≠ i := by
      intro h
      have : k = i.val := by simpa using congrArg Fin.val h
      omega
    have hkj : (⟨k, hk⟩ : Fin n) ≠ j := by
      intro h
      have : k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take i.val (transposePermutationValues perm i j).toList)[k] =
          (transposePermutationValues perm i j)[k]'hk := by
        simp [Vector.getElem_toList]
      _ = perm[k]'hk := by
        change (transposePermutationValues perm i j)[(⟨k, hk⟩ : Fin n)] =
          perm[(⟨k, hk⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm (finTranspose_of_ne i j ⟨k, hk⟩ hki hkj)
      _ = (List.take i.val perm.toList)[k] := by
        simp [Vector.getElem_toList]

private theorem transposePermutationValues_middle_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    ((transposePermutationValues perm i j).toList.drop (i.val + 1)).take
        (j.val - i.val - 1) =
      (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : i.val + 1 + k < n := by
      omega
    have hri : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : i.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : i.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take (j.val - i.val - 1)
          (List.drop (i.val + 1) (transposePermutationValues perm i j).toList))[k] =
          (transposePermutationValues perm i j)[i.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[i.val + 1 + k]'hrlt := by
        change (transposePermutationValues perm i j)[(⟨i.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨i.val + 1 + k, hrlt⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm
          (finTranspose_of_ne i j ⟨i.val + 1 + k, hrlt⟩ hri hrj)
      _ =
          (List.take (j.val - i.val - 1) (List.drop (i.val + 1) perm.toList))[k] := by
        simp [Vector.getElem_toList]

private theorem transposePermutationValues_drop_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList.drop (j.val + 1) =
      perm.toList.drop (j.val + 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : j.val + 1 + k < n := by
      omega
    have hri : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : j.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : j.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.drop (j.val + 1) (transposePermutationValues perm i j).toList)[k] =
          (transposePermutationValues perm i j)[j.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[j.val + 1 + k]'hrlt := by
        change (transposePermutationValues perm i j)[(⟨j.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨j.val + 1 + k, hrlt⟩ : Fin n)]
        rw [transposePermutationValues_get]
        exact vector_get_fin_congr perm
          (finTranspose_of_ne i j ⟨j.val + 1 + k, hrlt⟩ hri hrj)
      _ = (List.drop (j.val + 1) perm.toList)[k] := by
        simp [Vector.getElem_toList]

private theorem transposePermutationValues_toList_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (transposePermutationValues perm i j).toList =
      perm.toList.take i.val ++ perm[j] ::
        (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          perm[i] :: perm.toList.drop (j.val + 1) := by
  rw [vector_toList_split_two (transposePermutationValues perm i j) hij]
  rw [transposePermutationValues_take_of_lt perm hij]
  rw [transposePermutationValues_middle_of_lt perm hij]
  rw [transposePermutationValues_drop_of_lt perm hij]
  have hi : (transposePermutationValues perm i j)[i] = perm[j] := by
    rw [transposePermutationValues_get]
    exact vector_get_fin_congr perm (finTranspose_left i j)
  have hj : (transposePermutationValues perm i j)[j] = perm[i] := by
    rw [transposePermutationValues_get]
    exact vector_get_fin_congr perm (finTranspose_right i j)
  rw [hi, hj]

private theorem transposePermutationValues_toList_of_gt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hji : j.val < i.val) :
    (transposePermutationValues perm i j).toList =
      perm.toList.take j.val ++ perm[i] ::
        (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
          perm[j] :: perm.toList.drop (i.val + 1) := by
  have hcomm : transposePermutationValues perm i j = transposePermutationValues perm j i := by
    apply Vector.ext
    intro r hr
    change (transposePermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (transposePermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [transposePermutationValues_get]
    by_cases hri : (⟨r, hr⟩ : Fin n) = i
    · subst i
      exact vector_get_fin_congr perm
        ((finTranspose_left ⟨r, hr⟩ j).trans
          (finTranspose_right j ⟨r, hr⟩).symm)
    · by_cases hrj : (⟨r, hr⟩ : Fin n) = j
      · subst j
        exact vector_get_fin_congr perm
          ((finTranspose_right i ⟨r, hr⟩).trans
            (finTranspose_left ⟨r, hr⟩ i).symm)
      · exact vector_get_fin_congr perm
          ((finTranspose_of_ne i j ⟨r, hr⟩ hri hrj).trans
            (finTranspose_of_ne j i ⟨r, hr⟩ hrj hri).symm)
  rw [hcomm]
  exact
    (transposePermutationValues_toList_of_lt perm (i := j) (j := i) hji)

private theorem transposePermutationValues_involutive {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    transposePermutationValues (transposePermutationValues perm i j) i j = perm := by
  apply Vector.ext
  intro r hr
  simp [transposePermutationValues, finTranspose_involutive]

private theorem detSign_transposePermutationValues_involutive {R : Type u}
    [Lean.Grind.Ring R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) :
    detSign (R := R) (transposePermutationValues (transposePermutationValues perm i j) i j) =
      detSign (R := R) perm := by
  rw [transposePermutationValues_involutive]

private theorem inversionCount_transposePermutationValues_parity {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    inversionCount (transposePermutationValues perm i j).toList % 2 =
      (inversionCount perm.toList + 1) % 2 := by
  have hval : i.val ≠ j.val := by
    intro hv
    exact h (Fin.ext hv)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hnodup_split :
          (perm.toList.take i.val ++ perm[i] ::
              (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                perm[j] :: perm.toList.drop (j.val + 1)).Nodup := by
        rw [← vector_toList_split_two perm hij]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take i.val ++ perm[j] ::
                (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                  perm[i] :: perm.toList.drop (j.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          inversionCount_swap_separated_parity
            (perm.toList.take i.val)
            ((perm.toList.drop (i.val + 1)).take (j.val - i.val - 1))
            (perm.toList.drop (j.val + 1)) perm[i] perm[j] hnodup_split
        rw [← vector_toList_split_two perm hij] at hswap
        exact hswap
      rw [transposePermutationValues_toList_of_lt perm hij]
      exact hpar
  | inr hji =>
      have hnodup_split :
          (perm.toList.take j.val ++ perm[j] ::
              (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                perm[i] :: perm.toList.drop (i.val + 1)).Nodup := by
        rw [← vector_toList_split_two perm hji]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take j.val ++ perm[i] ::
                (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                  perm[j] :: perm.toList.drop (i.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          inversionCount_swap_separated_parity
            (perm.toList.take j.val)
            ((perm.toList.drop (j.val + 1)).take (i.val - j.val - 1))
            (perm.toList.drop (i.val + 1)) perm[j] perm[i] hnodup_split
        rw [← vector_toList_split_two perm hji] at hswap
        exact hswap
      rw [transposePermutationValues_toList_of_gt perm hji]
      exact hpar

private theorem detProduct_rowSwap_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) (perm : Vector (Fin n) n) :
    detProduct (rowSwap M i j) perm =
      detProduct M (transposePermutationValues perm i j) := by
  sorry

private theorem detSign_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (transposePermutationValues perm i j) := by
  unfold detSign
  have hpar :=
    inversionCount_transposePermutationValues_parity perm i j hnodup h
  by_cases hp : inversionCount perm.toList % 2 = 0
  · have ht : inversionCount (transposePermutationValues perm i j).toList % 2 ≠ 0 := by
      omega
    simp [hp, ht]
    grind
  · have hpone : inversionCount perm.toList % 2 = 1 := by
      have hlt : inversionCount perm.toList % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have ht : inversionCount (transposePermutationValues perm i j).toList % 2 = 0 := by
      omega
    simp [hp, ht]

private theorem detTerm_rowSwap_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j)
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    detTerm (rowSwap M i j) perm =
      -detTerm M (transposePermutationValues perm i j) := by
  unfold detTerm
  rw [detProduct_rowSwap_transposeValues M i j h perm]
  rw [detSign_transposeValues (R := R) perm i j hnodup h]
  grind

private theorem permutationVectors_transposeValues_neg_sum {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  sorry

/-- The permutation-vector enumeration contributes `1` on the identity
matrix: all non-identity terms vanish and the identity vector appears once. -/
private theorem permutationVectors_identity_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (1 : Matrix R n n) perm) 0 = 1 := by
  induction n with
  | zero =>
      simp [permutationVectors, emptyVec, detTerm, detSign, detProduct, inversionCount]
      grind
  | succ n ih =>
      simp only [permutationVectors]
      rw [foldl_det_sum_flatMap]
      simp only [List.foldl_map, foldl_detTerm_identity_insertions]
      exact ih

/-- Row swapping pairs the permutation-vector Leibniz terms with opposite sign. -/
private theorem permutationVectors_rowSwap_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + -detTerm M (transposePermutationValues perm i j)) 0 := by
        apply foldl_det_sum_congr
        intro perm hmem
        exact detTerm_rowSwap_transposeValues M i j h perm (permutationVectors_nodup hmem)
    _ = -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact permutationVectors_transposeValues_neg_sum M i j h

/-- Scaling one matrix row scales each Leibniz term by the same scalar. -/
private theorem detTerm_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detTerm (rowScale M i c) perm = c * detTerm M perm := by
  unfold detTerm
  rw [detProduct_rowScale]
  grind

private def rowAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  M.set dst M[src]

private theorem rowAdd_get {R : Type u} [Mul R] [Add R] {n : Nat}
    (M : Matrix R n n) (src dst r : Fin n) (c : R) (k : Fin n) :
    (rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [rowAdd]
  · simp [rowAdd, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]))[r] = M[r] := by
      exact
        (Vector.getElem_set_ne
          (xs := M) (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
          dst.isLt r.isLt hval)
    simpa [rowAdd] using congrArg (fun row => row[k]) hrow

private theorem rowAddDuplicate_get {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst r : Fin n) (k : Fin n) :
    (rowAddDuplicate M src dst)[r][k] =
      if r = dst then M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [rowAddDuplicate]
  · simp [rowAddDuplicate, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow : (M.set dst M[src])[r] = M[r] := by
      exact (Vector.getElem_set_ne (xs := M) (x := M[src]) dst.isLt r.isLt hval)
    simpa [rowAddDuplicate] using congrArg (fun row => row[k]) hrow

private theorem detProduct_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detProduct (rowAdd M src dst c) perm =
      detProduct M perm + c * detProduct (rowAddDuplicate M src dst) perm := by
  unfold detProduct
  calc
    (List.finRange n).foldl
        (fun acc r => acc * (rowAdd M src dst c)[r][perm[r]]) 1 =
      (List.finRange n).foldl
        (fun acc r =>
          acc * if r = dst then
            M[r][perm[r]] + c * (rowAddDuplicate M src dst)[r][perm[r]]
          else
            M[r][perm[r]]) 1 := by
        apply foldl_det_product_congr
        intro r _hmem
        by_cases h : r = dst
        · subst r
          rw [rowAdd_get M src dst dst c perm[dst]]
          rw [rowAddDuplicate_get M src dst dst perm[dst]]
          simp
        · rw [rowAdd_get, rowAddDuplicate_get]
          simp [h]
    _ =
      (List.finRange n).foldl (fun acc r => acc * M[r][perm[r]]) 1 +
        c * (List.finRange n).foldl
          (fun acc r => acc * (rowAddDuplicate M src dst)[r][perm[r]]) 1 := by
        exact foldl_det_product_single_add
          (List.finRange n) dst c
          (fun r => M[r][perm[r]])
          (fun r => (rowAddDuplicate M src dst)[r][perm[r]]) 1
          (List.mem_finRange dst) (List.nodup_finRange n)
          (fun r _hmem hne => by
            change (rowAddDuplicate M src dst)[r][perm[r]] = M[r][perm[r]]
            rw [rowAddDuplicate_get]
            simp [hne])

private theorem detTerm_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (perm : Vector (Fin n) n) :
    detTerm (rowAdd M src dst c) perm =
      detTerm M perm + c * detTerm (rowAddDuplicate M src dst) perm := by
  unfold detTerm
  rw [detProduct_rowAdd]
  grind

private theorem permutationVectors_duplicateRow_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAddDuplicate M src dst) perm) 0 = 0 := by
  sorry

/-- The multilinear expansion of a row addition has zero total duplicate-row
contribution, so the Leibniz sum is unchanged. -/
private theorem permutationVectors_rowAdd_sum {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm =>
          acc + (detTerm M perm + c * detTerm (rowAddDuplicate M src dst) perm)) 0 := by
        apply foldl_det_sum_congr
        intro perm _hmem
        exact detTerm_rowAdd M src dst c perm
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        (permutationVectors n).foldl
          (fun acc perm => acc + c * detTerm (rowAddDuplicate M src dst) perm) 0 := by
        exact foldl_det_sum_add_zero
          (permutationVectors n) (detTerm M) (fun perm => c * detTerm (rowAddDuplicate M src dst) perm)
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 +
        c * (permutationVectors n).foldl
          (fun acc perm => acc + detTerm (rowAddDuplicate M src dst) perm) 0 := by
        rw [foldl_det_sum_mul_left_zero]
    _ =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
        rw [permutationVectors_duplicateRow_sum M src dst h]
        grind

/-- The Leibniz sum for the identity matrix has exactly the identity
permutation as its nonzero contribution. -/
private theorem det_identity_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (1 : Matrix R n n) perm) 0 = 1 := by
  exact permutationVectors_identity_sum

/-- Swapping two rows pairs each Leibniz summand with the corresponding
transposed permutation and flips the computed inversion parity. -/
private theorem det_rowSwap_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowSwap M i j) perm) 0 =
      -((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  exact permutationVectors_rowSwap_sum M i j h

/-- Scaling one row factors the scalar out of every nonzero Leibniz summand. -/
private theorem det_rowScale_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowScale M i c) perm) 0 =
      c * ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
  calc
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowScale M i c) perm) 0 =
      (permutationVectors n).foldl
        (fun acc perm => acc + c * detTerm M perm) 0 := by
        apply foldl_det_sum_congr
        intro perm _hmem
        exact detTerm_rowScale M i c perm
    _ = c * ((permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0) := by
        exact foldl_det_sum_mul_left_zero (permutationVectors n) c (detTerm M)

/-- Adding a multiple of one row to a distinct row leaves the Leibniz sum
unchanged; the extra multilinear contribution has two equal rows. -/
private theorem det_rowAdd_leibniz {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    (permutationVectors n).foldl
        (fun acc perm => acc + detTerm (rowAdd M src dst c) perm) 0 =
      (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0 := by
  exact permutationVectors_rowAdd_sum M src dst c h

theorem det_one {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    det (1 : Matrix R n n) = 1 := by
  simpa [det] using (det_identity_leibniz (R := R) (n := n))

theorem det_rowSwap {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (rowSwap M i j) = -det M := by
  simpa [det] using det_rowSwap_leibniz M i j h

theorem det_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    det (rowScale M i c) = c * det M := by
  simpa [det] using det_rowScale_leibniz M i c

theorem det_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (rowAdd M src dst c) = det M := by
  simpa [det] using det_rowAdd_leibniz M src dst c h

end Matrix
end Hex
