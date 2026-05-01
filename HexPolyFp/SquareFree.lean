import HexModArith.Prime
import HexPolyFp.Basic

/-!
Executable square-free decomposition for `F_p[x]`.

This module implements a Yun-style square-free decomposition for
`Hex.FpPoly p`, recording the unit factor and the positive-multiplicity
square-free factors obtained from repeated gcd/derivative steps and
`p`-th-root descent in characteristic `p`. The public API carries an
explicit `Hex.Nat.Prime p` contract because the exported factorization and
square-free theorems are intended for prime-field coefficients.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- One square-free factor together with its multiplicity. -/
structure SquareFreeFactor (p : Nat) [ZMod64.Bounds p] where
  factor : FpPoly p
  multiplicity : Nat

/-- A square-free decomposition records the scalar unit and the nonconstant factors. -/
structure SquareFreeDecomposition (p : Nat) [ZMod64.Bounds p] where
  unit : ZMod64 p
  factors : List (SquareFreeFactor p)

/-- Detect the unit polynomial `1`. -/
private def isOne (f : FpPoly p) : Bool :=
  match f.degree? with
  | some 0 =>
      if f.coeff 0 = (1 : ZMod64 p) then
        true
      else
        false
  | _ => false

/-- Polynomial exponentiation uses square-and-multiply on the exponent bits. -/
private def pow (f : FpPoly p) (n : Nat) : FpPoly p :=
  let rec go (acc base : FpPoly p) (k : Nat) : FpPoly p :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then acc * base else acc
      go acc' (base * base) (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go 1 f n

private theorem pow_one (f : FpPoly p) :
    pow f 1 = f := by
  unfold pow
  simp [pow.go]

private def powLinear (f : FpPoly p) : Nat → FpPoly p
  | 0 => 1
  | n + 1 => powLinear f n * f

private theorem powLinear_add (f : FpPoly p) (m n : Nat) :
    powLinear f (m + n) = powLinear f m * powLinear f n := by
  induction n with
  | zero =>
      simp [powLinear]
  | succ n ih =>
      rw [Nat.add_succ, powLinear, ih, powLinear]
      exact DensePoly.mul_assoc_poly (powLinear f m) (powLinear f n) f

private theorem powLinear_double (f : FpPoly p) (n : Nat) :
    powLinear f (2 * n) = powLinear (f * f) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have htwo : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [htwo]
      change powLinear f ((2 * n + 1) + 1) =
        powLinear (f * f) n * (f * f)
      rw [powLinear, powLinear, ih]
      exact DensePoly.mul_assoc_poly (powLinear (f * f) n) f f

private theorem powLinear_double_add_one (f : FpPoly p) (n : Nat) :
    powLinear f (2 * n + 1) = f * powLinear (f * f) n := by
  rw [powLinear, powLinear_double]
  exact mul_comm (powLinear (f * f) n) f

private theorem pow_go_eq_mul_powLinear (acc base : FpPoly p) (k : Nat) :
    pow.go acc base k = acc * powLinear base k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | ind k ih =>
      rw [pow.go.eq_def]
      by_cases hk : k = 0
      · simp [hk, powLinear]
      · rw [dif_neg hk]
        have hlt : k / 2 < k :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide : 1 < 2)
        cases Nat.mod_two_eq_zero_or_one k with
        | inl hmod0 =>
            have hk_eq : k = 2 * (k / 2) := by
              have h := Nat.mod_add_div k 2
              omega
            have hnot : ¬k % 2 = 1 := by omega
            have hdiv : 2 * (k / 2) / 2 = k / 2 :=
              Nat.mul_div_right (k / 2) (by decide : 0 < 2)
            rw [if_neg hnot]
            calc
              pow.go acc (base * base) (k / 2)
                  = acc * powLinear (base * base) (k / 2) := by
                    exact ih (k / 2) hlt acc (base * base)
              _ = acc * powLinear base k := by
                    rw [hk_eq, hdiv, powLinear_double]
        | inr hmod1 =>
            have hk_eq : k = 2 * (k / 2) + 1 := by
              have h := Nat.mod_add_div k 2
              omega
            rw [if_pos hmod1]
            calc
              pow.go (acc * base) (base * base) (k / 2)
                  = (acc * base) * powLinear (base * base) (k / 2) := by
                    exact ih (k / 2) hlt (acc * base) (base * base)
              _ = acc * (base * powLinear (base * base) (k / 2)) := by
                    exact DensePoly.mul_assoc_poly acc base
                      (powLinear (base * base) (k / 2))
              _ = acc * powLinear base (2 * (k / 2) + 1) := by
                    rw [powLinear_double_add_one]
              _ = acc * powLinear base k := by
                    rw [← hk_eq]

private theorem pow_eq_powLinear (f : FpPoly p) (n : Nat) :
    pow f n = powLinear f n := by
  unfold pow
  rw [pow_go_eq_mul_powLinear]
  exact one_mul (powLinear f n)

private theorem powLinear_powLinear_mul (f : FpPoly p) (m n : Nat) :
    powLinear (powLinear f n) m = powLinear f (m * n) := by
  induction m with
  | zero =>
      simp [powLinear]
  | succ m ih =>
      rw [powLinear, ih]
      simpa [Nat.succ_mul] using (powLinear_add f (m * n) n).symm

private theorem zmod64_add_pow_prime
    (hp : Hex.Nat.Prime p) (a b : ZMod64 p) :
    (a + b) ^ p = a ^ p + b ^ p := by
  rw [ZMod64.pow_prime hp (a + b), ZMod64.pow_prime hp a, ZMod64.pow_prime hp b]

private theorem zmod64_fold_add_pow_prime_acc
    (hp : Hex.Nat.Prime p) (xs : List (ZMod64 p)) (acc : ZMod64 p) :
    (xs.foldl (fun acc x => acc + x) acc) ^ p =
      (xs.map fun x => x ^ p).foldl (fun acc x => acc + x) (acc ^ p) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih (acc + x), zmod64_add_pow_prime hp acc x]

private theorem zmod64_fold_add_pow_prime
    (hp : Hex.Nat.Prime p) (xs : List (ZMod64 p)) :
    (xs.foldl (fun acc x => acc + x) 0) ^ p =
      (xs.map fun x => x ^ p).foldl (fun acc x => acc + x) 0 := by
  simpa [ZMod64.pow_prime hp (0 : ZMod64 p)] using
    zmod64_fold_add_pow_prime_acc (p := p) hp xs (0 : ZMod64 p)

private theorem zmod64_index_fold_add_pow_prime
    (hp : Hex.Nat.Prime p) (xs : List Nat) (term : Nat → ZMod64 p) :
    (xs.foldl (fun acc i => acc + term i) 0) ^ p =
      xs.foldl (fun acc i => acc + term i ^ p) 0 := by
  simpa [List.foldl_map] using
    zmod64_fold_add_pow_prime (p := p) hp (xs.map term)

/-- Multiply the factors in a square-free decomposition with their multiplicities. -/
def weightedProduct (factors : List (SquareFreeFactor p)) : FpPoly p :=
  factors.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) 1

private theorem weightedProduct_nil :
    weightedProduct ([] : List (SquareFreeFactor p)) = 1 := by
  rfl

private theorem weightedProduct_foldl_eq_mul
    (acc : FpPoly p) (factors : List (SquareFreeFactor p)) :
    factors.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) acc =
      acc * weightedProduct factors := by
  induction factors generalizing acc with
  | nil =>
      rw [weightedProduct_nil]
      exact (DensePoly.mul_one_right_poly acc).symm
  | cons sf factors ih =>
      unfold weightedProduct
      simp only [List.foldl_cons]
      rw [ih (acc * pow sf.factor sf.multiplicity)]
      rw [ih ((1 : FpPoly p) * pow sf.factor sf.multiplicity)]
      have hone :
          (1 : FpPoly p) * pow sf.factor sf.multiplicity =
            pow sf.factor sf.multiplicity := by
        exact one_mul (pow sf.factor sf.multiplicity)
      rw [hone]
      exact DensePoly.mul_assoc_poly acc (pow sf.factor sf.multiplicity) (weightedProduct factors)

private theorem weightedProduct_cons
    (sf : SquareFreeFactor p) (factors : List (SquareFreeFactor p)) :
    weightedProduct (sf :: factors) =
      pow sf.factor sf.multiplicity * weightedProduct factors := by
  unfold weightedProduct
  simp only [List.foldl_cons]
  rw [weightedProduct_foldl_eq_mul]
  exact congrArg (fun x => x * weightedProduct factors) (one_mul (pow sf.factor sf.multiplicity))

private theorem weightedProduct_append
    (left right : List (SquareFreeFactor p)) :
    weightedProduct (left ++ right) = weightedProduct left * weightedProduct right := by
  unfold weightedProduct
  rw [List.foldl_append]
  simpa [weightedProduct] using
    weightedProduct_foldl_eq_mul
      (p := p)
      (left.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) 1)
      right

private theorem weightedProduct_singleton (sf : SquareFreeFactor p) :
    weightedProduct [sf] = pow sf.factor sf.multiplicity := by
  rw [weightedProduct_cons, weightedProduct_nil]
  exact DensePoly.mul_one_right_poly (pow sf.factor sf.multiplicity)

private theorem weightedProduct_reverse_cons
    (sf : SquareFreeFactor p) (accRev : List (SquareFreeFactor p)) :
    weightedProduct (sf :: accRev).reverse =
      weightedProduct accRev.reverse * pow sf.factor sf.multiplicity := by
  rw [List.reverse_cons, weightedProduct_append, weightedProduct_singleton]

/--
Extract the formal `p`-th root by keeping exactly the coefficients whose
degrees are multiples of `p`.
-/
private def pthRoot (f : FpPoly p) : FpPoly p :=
  let rootSize := (f.size + p - 1) / p
  ofCoeffs <|
    (List.range rootSize).map (fun i => f.coeff (i * p)) |>.toArray

private theorem pthRoot_coeff_of_lt
    (f : FpPoly p) {i : Nat} (hi : i < (f.size + p - 1) / p) :
    (pthRoot f).coeff i = f.coeff (i * p) := by
  unfold pthRoot ofCoeffs
  rw [DensePoly.coeff_ofCoeffs]
  simp [Array.getD, hi]

private theorem pthRoot_coeff (f : FpPoly p) (i : Nat) :
    (pthRoot f).coeff i = f.coeff (i * p) := by
  by_cases hi : i < (f.size + p - 1) / p
  · exact pthRoot_coeff_of_lt f hi
  · unfold pthRoot ofCoeffs
    rw [DensePoly.coeff_ofCoeffs]
    simp [Array.getD, hi]
    exact (DensePoly.coeff_eq_zero_of_size_le f (by
      have hp : 0 < p := ZMod64.Bounds.pPos (p := p)
      have hle : (f.size + p - 1) / p ≤ i := Nat.le_of_not_gt hi
      have hraw : f.size + p - 1 ≤ i * p + p - 1 :=
        (Nat.div_le_iff_le_mul hp).mp hle
      omega)).symm

private theorem zmod64_add_zero_coeff (a : ZMod64 p) :
    a + 0 = a := by
  grind

private theorem zmod64_zero_add_coeff (a : ZMod64 p) :
    0 + a = a := by
  grind

private theorem zmod64_add_zero_zero_coeff :
    (0 : ZMod64 p) + 0 = 0 := by
  grind

/-- The single coefficient contribution `g_i x^i`, represented with dense shifts. -/
private def coeffTerm (g : FpPoly p) (i : Nat) : FpPoly p :=
  DensePoly.shift i (DensePoly.scale (g.coeff i) (1 : FpPoly p))

/-- Finite sum of the coefficient contributions of `g` below the bound `m`. -/
private def coeffFold (g : FpPoly p) (m : Nat) : FpPoly p :=
  (List.range m).foldl (fun acc i => acc + coeffTerm g i) 0

/-- Project a monomial coefficient contribution back to a dense coefficient. -/
private theorem coeffTerm_coeff (g : FpPoly p) (i n : Nat) :
    (coeffTerm g i).coeff n = if n = i then g.coeff i else 0 := by
  unfold coeffTerm
  have hzero : g.coeff i * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_shift_scale i (g.coeff i) (1 : FpPoly p) n hzero]
  by_cases hlt : n < i
  · simp only [hlt, if_true]
    have hne : n ≠ i := by omega
    simp [hne]
    rfl
  · simp only [hlt, if_false]
    change g.coeff i * (DensePoly.C (1 : ZMod64 p)).coeff (n - i) =
      if n = i then g.coeff i else 0
    rw [DensePoly.coeff_C]
    by_cases hni : n = i
    · simp [hni]
      grind
    · have hsub : n - i ≠ 0 := by omega
      simp [hni, hsub]
      exact hzero

private theorem coeff_foldl_coeffTerm_coeff
    (g : FpPoly p) (xs : List Nat) (acc : FpPoly p) (n : Nat) :
    (xs.foldl (fun acc i => acc + coeffTerm g i) acc).coeff n =
      xs.foldl (fun acc i => acc + (coeffTerm g i).coeff n) (acc.coeff n) := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + coeffTerm g i)]
      rw [DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_coeff]

private theorem coeffFold_coeff_index_fold (g : FpPoly p) (m n : Nat) :
    (coeffFold g m).coeff n =
      (List.range m).foldl (fun acc i => acc + (coeffTerm g i).coeff n) 0 := by
  unfold coeffFold
  simpa [DensePoly.coeff_zero] using
    coeff_foldl_coeffTerm_coeff (p := p) g (List.range m) (0 : FpPoly p) n

private theorem coeffFold_coeff_index_fold_pow_prime
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) :
    ((coeffFold g m).coeff n) ^ p =
      (List.range m).foldl
        (fun acc i => acc + (coeffTerm g i).coeff n ^ p) 0 := by
  rw [coeffFold_coeff_index_fold]
  exact zmod64_index_fold_add_pow_prime
    (p := p) hp (List.range m) (fun i => (coeffTerm g i).coeff n)

private theorem powLinear_coeffTerm_coeff (g : FpPoly p) (i k n : Nat) :
    (powLinear (coeffTerm g i) k).coeff n =
      if n = k * i then (g.coeff i) ^ k else 0 := by
  induction k generalizing n with
  | zero =>
      simp [powLinear]
      change (DensePoly.C (1 : ZMod64 p)).coeff n =
        if n = 0 then (g.coeff i) ^ 0 else 0
      rw [DensePoly.coeff_C]
      by_cases hn : n = 0
      · simp [hn, Lean.Grind.Semiring.pow_zero (g.coeff i)]
      · simp [hn]
        change (0 : ZMod64 p) = (0 : ZMod64 p)
        rfl
  | succ k ih =>
      rw [powLinear]
      change (powLinear (coeffTerm g i) k *
          DensePoly.shift i (DensePoly.scale (g.coeff i) (1 : FpPoly p))).coeff n =
        if n = (k + 1) * i then (g.coeff i) ^ (k + 1) else 0
      rw [coeff_mul_shift_scale_one]
      by_cases hin : i ≤ n
      · rw [if_pos hin, ih]
        by_cases hprev : n - i = k * i
        · have hn : n = (k + 1) * i := by
            calc
              n = n - i + i := (Nat.sub_add_cancel hin).symm
              _ = k * i + i := by rw [hprev]
              _ = (k + 1) * i := by rw [Nat.succ_mul]
          rw [if_pos hprev, if_pos hn]
          exact (Lean.Grind.Semiring.pow_succ (g.coeff i) k).symm
        · have hn : n ≠ (k + 1) * i := by
            intro hn
            apply hprev
            calc
              n - i = (k + 1) * i - i := by rw [hn]
              _ = k * i := by rw [Nat.succ_mul]; omega
          rw [if_neg hprev, if_neg hn]
          grind
      · have hn : n ≠ (k + 1) * i := by
          intro hn
          have hki : i ≤ (k + 1) * i := by
            rw [Nat.succ_mul]
            omega
          omega
        rw [if_neg hin, if_neg hn]

/-- Coefficient projection for the bounded finite coefficient fold. -/
private theorem coeffFold_coeff (g : FpPoly p) (m n : Nat) :
    (coeffFold g m).coeff n = if n < m then g.coeff n else 0 := by
  induction m with
  | zero =>
      unfold coeffFold
      simp only [List.range_zero, List.foldl_nil]
      rw [DensePoly.coeff_zero]
      simp
      rfl
  | succ m ih =>
      unfold coeffFold
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change ((List.range m).foldl (fun acc i => acc + coeffTerm g i) 0 +
          coeffTerm g m).coeff n = if n < m + 1 then g.coeff n else 0
      rw [DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_coeff]
      change (coeffFold g m).coeff n + (coeffTerm g m).coeff n =
        if n < m + 1 then g.coeff n else 0
      rw [ih, coeffTerm_coeff]
      by_cases hlt : n < m
      · rw [if_pos hlt]
        have hne : n ≠ m := by omega
        rw [if_neg hne]
        rw [if_pos (by omega : n < m + 1)]
        exact zmod64_add_zero_coeff (g.coeff n)
      · by_cases heq : n = m
        · rw [if_neg hlt]
          rw [if_pos heq]
          rw [if_pos (by omega : n < m + 1)]
          rw [heq]
          exact zmod64_zero_add_coeff (g.coeff m)
        · have hsucc : ¬n < m + 1 := by omega
          rw [if_neg hlt]
          rw [if_neg heq]
          rw [if_neg hsucc]
          exact zmod64_add_zero_zero_coeff

/-- Any coefficient fold whose bound reaches `g.size` reconstructs `g`. -/
private theorem coeffFold_eq_of_size_le (g : FpPoly p) (m : Nat) (hm : g.size ≤ m) :
    coeffFold g m = g := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeffFold_coeff]
  by_cases hn : n < m
  · simp [hn]
  · simp [hn]
    exact (DensePoly.coeff_eq_zero_of_size_le g (by omega)).symm

/-- Reconstruct a polynomial from exactly its stored coefficient range. -/
private theorem coeffFold_size_eq (g : FpPoly p) :
    coeffFold g g.size = g := by
  exact coeffFold_eq_of_size_le g g.size (Nat.le_refl g.size)

/--
Coefficient expansion for a power of a bounded coefficient fold.

The successor case is the finite schoolbook convolution of the already
expanded `k` choices with one more bounded coefficient choice from `g`.
-/
private def coeffFoldPowerCoeff (g : FpPoly p) (m : Nat) : Nat → Nat → ZMod64 p
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n =>
      (List.range (powLinear (coeffFold g m) k).size).foldl
        (fun acc i =>
          acc + coeffFoldPowerCoeff g m k i *
            (if n < i then 0 else if n - i < m then g.coeff (n - i) else 0))
        0

private theorem powLinear_coeffFold_coeff_expansion (g : FpPoly p) (m k n : Nat) :
    (powLinear (coeffFold g m) k).coeff n = coeffFoldPowerCoeff g m k n := by
  induction k generalizing n with
  | zero =>
      simp [powLinear, coeffFoldPowerCoeff]
      change (DensePoly.C (1 : ZMod64 p)).coeff n = if n = 0 then 1 else 0
      exact DensePoly.coeff_C (1 : ZMod64 p) n
  | succ k ih =>
      rw [powLinear, coeff_mul]
      unfold mulCoeffSum
      simp only [coeffFoldPowerCoeff]
      let xs := List.range (powLinear (coeffFold g m) k).size
      change xs.foldl
          (fun acc i => acc + mulCoeffTerm (powLinear (coeffFold g m) k) (coeffFold g m) n i)
          0 =
        xs.foldl
          (fun acc i =>
            acc + coeffFoldPowerCoeff g m k i *
              (if n < i then 0 else if n - i < m then g.coeff (n - i) else 0))
          0
      suffices hfold :
          ∀ acc,
            xs.foldl
                (fun acc i =>
                  acc + mulCoeffTerm (powLinear (coeffFold g m) k) (coeffFold g m) n i)
                acc =
              xs.foldl
                (fun acc i =>
                  acc + coeffFoldPowerCoeff g m k i *
                    (if n < i then 0 else if n - i < m then g.coeff (n - i) else 0))
                acc by
        exact hfold 0
      intro acc
      induction xs generalizing acc with
      | nil =>
          rfl
      | cons i xs ihxs =>
          simp only [List.foldl_cons]
          have hterm :
              mulCoeffTerm (powLinear (coeffFold g m) k) (coeffFold g m) n i =
                coeffFoldPowerCoeff g m k i *
                  (if n < i then 0 else if n - i < m then g.coeff (n - i) else 0) := by
            unfold mulCoeffTerm
            rw [ih, coeffFold_coeff]
            by_cases hni : n < i
            · simp [hni]
              grind
            · simp [hni]
          rw [hterm]
          exact ihxs _

private theorem powLinear_coeffFold_prime_coeff_expansion (g : FpPoly p) (m n : Nat) :
    (powLinear (coeffFold g m) p).coeff n = coeffFoldPowerCoeff g m p n :=
  powLinear_coeffFold_coeff_expansion g m p n

/--
Prime-characteristic cancellation for the recursive coefficient expansion of
`(coeffFold g m)^p`: all mixed `p`-tuples vanish, leaving only diagonal
choices from the bounded coefficient fold.
-/
private theorem coeffFoldPowerCoeff_prime_coeff
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) :
    coeffFoldPowerCoeff g m p n =
      if n % p = 0 then
        if n / p < m then (g.coeff (n / p)) ^ p else 0
      else
        0 := by
  sorry

private theorem coeffFoldPowerCoeff_prime_coeff_of_mod_ne_zero
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) (hn : n % p ≠ 0) :
    coeffFoldPowerCoeff g m p n = 0 := by
  rw [coeffFoldPowerCoeff_prime_coeff hp g m n]
  simp [hn]

private theorem coeffFoldPowerCoeff_prime_coeff_of_mod_eq_zero
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) (hn : n % p = 0) :
    coeffFoldPowerCoeff g m p n =
      if n / p < m then (g.coeff (n / p)) ^ p else 0 := by
  rw [coeffFoldPowerCoeff_prime_coeff hp g m n]
  simp [hn]

private theorem powLinear_coeffFold_prime_coeff
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m n : Nat) :
    (powLinear (coeffFold g m) p).coeff n =
      if n % p = 0 then
        if n / p < m then (g.coeff (n / p)) ^ p else 0
      else
        0 := by
  rw [powLinear_coeffFold_prime_coeff_expansion]
  exact coeffFoldPowerCoeff_prime_coeff hp g m n

private theorem powLinear_add_prime_coeff
    (hp : Hex.Nat.Prime p) (f g : FpPoly p) (n : Nat) :
    (powLinear (f + g) p).coeff n =
      (powLinear f p).coeff n + (powLinear g p).coeff n := by
  let m := max f.size g.size
  have hf_bound : f.size ≤ m := by
    exact Nat.le_max_left f.size g.size
  have hg_bound : g.size ≤ m := by
    exact Nat.le_max_right f.size g.size
  have hf_eq : coeffFold f m = f :=
    coeffFold_eq_of_size_le f m hf_bound
  have hg_eq : coeffFold g m = g :=
    coeffFold_eq_of_size_le g m hg_bound
  have hfg_eq : coeffFold (f + g) m = f + g := by
    apply DensePoly.ext_coeff
    intro i
    rw [coeffFold_coeff]
    by_cases hi : i < m
    · rw [if_pos hi]
    · rw [if_neg hi]
      have hfi : f.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le f (by omega)
      have hgi : g.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le g (by omega)
      rw [DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_coeff, hfi, hgi]
      exact zmod64_add_zero_zero_coeff.symm
  calc
    (powLinear (f + g) p).coeff n =
        (powLinear (coeffFold (f + g) m) p).coeff n := by
          rw [hfg_eq]
    _ = (powLinear (coeffFold f m) p).coeff n +
          (powLinear (coeffFold g m) p).coeff n := by
          rw [powLinear_coeffFold_prime_coeff hp (f + g) m n]
          rw [powLinear_coeffFold_prime_coeff hp f m n]
          rw [powLinear_coeffFold_prime_coeff hp g m n]
          by_cases hn : n % p = 0
          · rw [if_pos hn, if_pos hn, if_pos hn]
            by_cases hdiv : n / p < m
            · rw [if_pos hdiv, if_pos hdiv, if_pos hdiv]
              rw [DensePoly.coeff_add _ _ _ zmod64_add_zero_zero_coeff]
              exact zmod64_add_pow_prime hp (f.coeff (n / p)) (g.coeff (n / p))
            · rw [if_neg hdiv, if_neg hdiv, if_neg hdiv]
              exact zmod64_add_zero_zero_coeff.symm
          · rw [if_neg hn, if_neg hn, if_neg hn]
            exact zmod64_add_zero_zero_coeff.symm
    _ = (powLinear f p).coeff n + (powLinear g p).coeff n := by
          rw [hf_eq, hg_eq]

/--
Freshman's-dream coefficient support for a `p`th power over `F_p[x]`.
This is the dense-polynomial convolution fact needed by the formal
`p`-th-root reconstruction: only exponent tuples with all mass on one
input coefficient survive modulo `p`.
-/
private theorem powLinear_prime_coeff
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (n : Nat) :
    (powLinear g p).coeff n =
      if n % p = 0 then g.coeff (n / p) ^ p else 0 := by
  calc
    (powLinear g p).coeff n =
        (powLinear (coeffFold g g.size) p).coeff n := by
          rw [coeffFold_size_eq g]
    _ =
        if n % p = 0 then
          if n / p < g.size then (g.coeff (n / p)) ^ p else 0
        else
          0 := by
            exact powLinear_coeffFold_prime_coeff hp g g.size n
    _ = if n % p = 0 then g.coeff (n / p) ^ p else 0 := by
          by_cases hn : n % p = 0
          · rw [if_pos hn]
            by_cases hsize : n / p < g.size
            · rw [if_pos hsize]
              rw [if_pos hn]
            · rw [if_neg hsize]
              have hcoeff : g.coeff (n / p) = 0 :=
                DensePoly.coeff_eq_zero_of_size_le g (by omega)
              rw [hcoeff]
              rw [if_pos hn]
              exact (ZMod64.pow_prime hp (0 : ZMod64 p)).symm
          · rw [if_neg hn]
            rw [if_neg hn]

/--
Coefficient form of the prime-field Frobenius law for the formal `p`-th root:
the `p`th power restores coefficients in degrees divisible by `p` and has zero
coefficients elsewhere.
-/
private theorem pthRoot_pow_prime_coeff
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (n : Nat) :
    (pow (pthRoot f) p).coeff n =
      if n % p = 0 then f.coeff n else 0 := by
  rw [pow_eq_powLinear, powLinear_prime_coeff hp]
  by_cases hn : n % p = 0
  · simp [hn]
    have hmul : n / p * p = n := by
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hn))
    rw [pthRoot_coeff, hmul]
    exact ZMod64.pow_prime hp (f.coeff n)
  · simp [hn]

private theorem scale_one_poly (c : ZMod64 p) :
    DensePoly.scale c (1 : FpPoly p) = DensePoly.C c := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  change c * (DensePoly.C (1 : ZMod64 p)).coeff n = (DensePoly.C c).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n => exact hzero

private theorem C_mul_eq_scale (c : ZMod64 p) (f : FpPoly p) :
    DensePoly.C c * f = DensePoly.scale c f := by
  have hscale := scale_mul_left c (1 : FpPoly p) f
  rw [one_mul, scale_one_poly] at hscale
  exact hscale.symm

private theorem scale_scale (c d : ZMod64 p) (f : FpPoly p) :
    DensePoly.scale c (DensePoly.scale d f) = DensePoly.scale (c * d) f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
  have hzero_d : d * (0 : ZMod64 p) = 0 := by grind
  have hzero_cd : (c * d) * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero_c]
  rw [DensePoly.coeff_scale _ _ _ hzero_d]
  rw [DensePoly.coeff_scale _ _ _ hzero_cd]
  grind

private theorem scale_one_left (f : FpPoly p) :
    DensePoly.scale (1 : ZMod64 p) f = f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : (1 : ZMod64 p) * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  grind

private theorem zmod64_coprime_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    Nat.Coprime a.toNat p := by
  rw [Nat.Coprime]
  have hnot_dvd : ¬ p ∣ a.toNat := by
    intro hdiv
    rcases hdiv with ⟨k, hk⟩
    have ha_pos : 0 < a.toNat := by
      by_cases hnat : a.toNat = 0
      · exfalso
        apply ha
        apply ZMod64.ext
        apply UInt64.toNat_inj.mp
        simpa [ZMod64.toNat_eq_val] using hnat
      · exact Nat.pos_of_ne_zero hnat
    have hk_pos : 0 < k := by
      cases k with
      | zero =>
          exfalso
          have : a.toNat = 0 := by simpa using hk
          omega
      | succ k => exact Nat.succ_pos k
    have hle : p ≤ a.toNat := by
      rw [hk]
      simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left p hk_pos
    exact (Nat.not_le_of_gt a.toNat_lt) hle
  have hgcd_dvd_p : Nat.gcd a.toNat p ∣ p := Nat.gcd_dvd_right a.toNat p
  rcases hp.2 (Nat.gcd a.toNat p) hgcd_dvd_p with hgcd | hgcd
  · exact hgcd
  · exfalso
    apply hnot_dvd
    rcases Nat.gcd_dvd_left a.toNat p with ⟨k, hk⟩
    rw [hgcd] at hk
    exact ⟨k, hk⟩

private theorem zmod64_mul_inv_eq_one_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have hcop := zmod64_coprime_of_prime_ne_zero hp ha
  have hinv : (a⁻¹ * a).toNat = (1 : ZMod64 p).toNat := by
    simpa [ZMod64.toNat_one] using ZMod64.inv_mul_eq_one (p := p) a hcop
  have hcomm : a * a⁻¹ = a⁻¹ * a := by grind
  rw [hcomm]
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  simpa [ZMod64.toNat_eq_val] using hinv

private theorem zmod64_one_ne_zero_of_prime
    (hp : Hex.Nat.Prime p) :
    (1 : ZMod64 p) ≠ 0 := by
  intro hone
  have hnat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat hone
  change (ZMod64.one : ZMod64 p).toNat = (ZMod64.zero : ZMod64 p).toNat at hnat
  have hp_gt : 1 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  rw [ZMod64.toNat_one, ZMod64.toNat_zero, Nat.mod_eq_of_lt hp_gt] at hnat
  omega

private theorem zmod64_inv_ne_zero_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    a⁻¹ ≠ 0 := by
  intro hinv
  have hone := zmod64_mul_inv_eq_one_of_prime_ne_zero hp ha
  rw [hinv] at hone
  have hzero : a * (0 : ZMod64 p) = 0 := by grind
  rw [hzero] at hone
  exact zmod64_one_ne_zero_of_prime hp hone.symm

private theorem zmod64_mul_zero (a : ZMod64 p) :
    a * 0 = 0 := by
  grind

private theorem leadingCoeff_ne_zero_of_isZero_false
    (f : FpPoly p) (hzero : f.isZero = false) :
    DensePoly.leadingCoeff f ≠ 0 := by
  have hpos : 0 < f.size := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
      Nat.pos_iff_ne_zero] using hzero
  have hlast := DensePoly.coeff_last_ne_zero_of_pos_size f hpos
  have hlead : DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
    unfold DensePoly.leadingCoeff DensePoly.coeff
    rw [Array.back?_eq_getElem?]
    have hidx : f.coeffs.size - 1 < f.coeffs.size := by
      simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
    simp [Array.getD, DensePoly.size, hidx]
  rw [hlead]
  exact hlast

/-- Split off the leading coefficient so the recursive Yun loop can work on a monic input. -/
private def normalizeMonic (f : FpPoly p) : ZMod64 p × FpPoly p :=
  if f.isZero then
    (0, 0)
  else
    let unit := DensePoly.leadingCoeff f
    (unit, DensePoly.scale unit⁻¹ f)

private theorem normalizeMonic_zero
    (f : FpPoly p) (hzero : f.isZero = true) :
    normalizeMonic f = (0, 0) := by
  simp [normalizeMonic, hzero]

private theorem eq_zero_of_isZero_true
    (f : FpPoly p) (hzero : f.isZero = true) :
    f = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hsize : f.size = 0 := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hzero
  rw [DensePoly.coeff_eq_zero_of_size_le f (by omega)]
  exact DensePoly.coeff_zero n

private theorem normalizeMonic_zero_reconstruct
    (f : FpPoly p) (hzero : f.isZero = true) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  rw [normalizeMonic_zero f hzero]
  rw [eq_zero_of_isZero_true f hzero]
  exact mul_zero (DensePoly.C (0 : ZMod64 p))

private theorem normalizeMonic_nonzero
    (f : FpPoly p) (hzero : f.isZero = false) :
    normalizeMonic f =
      (DensePoly.leadingCoeff f, DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) := by
  simp [normalizeMonic, hzero]

private theorem normalizeMonic_nonzero_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  rw [normalizeMonic_nonzero f hzero]
  rw [C_mul_eq_scale, scale_scale]
  have hlead_ne := leadingCoeff_ne_zero_of_isZero_false f hzero
  rw [zmod64_mul_inv_eq_one_of_prime_ne_zero hp hlead_ne]
  exact scale_one_left f

private theorem normalizeMonic_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  cases hzero : f.isZero
  · exact normalizeMonic_nonzero_reconstruct hp f hzero
  · exact normalizeMonic_zero_reconstruct f hzero

/--
Yun's inner loop: peel off the factors with multiplicities `i`, `i + 1`, ...
from the coprime/repeated split `(c, w)`, consing each discovered factor onto
the reverse-order accumulator.
-/
private def yunFactors
    (c w : FpPoly p) (i : Nat) (fuel : Nat)
    (accRev : List (SquareFreeFactor p)) :
    List (SquareFreeFactor p) × FpPoly p :=
  match fuel with
  | 0 => (accRev, w)
  | fuel + 1 =>
      if isOne c then
        (accRev, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let accRev' :=
          if isOne z then
            accRev
          else
            { factor := z, multiplicity := i } :: accRev
        yunFactors y (w / y) (i + 1) fuel accRev'

/--
Specification payload for `yunFactors`: the first component is the product
contributed by factors discovered from `(c, w, i, fuel)`, and the second is
the repeated part that remains for the `p`-th-root descent.
-/
private def yunFactorsContribution
    (c w : FpPoly p) (i : Nat) : Nat → FpPoly p × FpPoly p
  | 0 => (1, w)
  | fuel + 1 =>
      if isOne c then
        (1, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let tail := yunFactorsContribution y (w / y) (i + 1) fuel
        let contribution :=
          if isOne z then
            tail.1
          else
            pow z i * tail.1
        (contribution, tail.2)

private theorem yunFactors_reconstruction_invariant
    (c w : FpPoly p) (i fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    let loop := yunFactors c w i fuel accRev
    let contribution := yunFactorsContribution c w i fuel
    loop.2 = contribution.2 ∧
      weightedProduct loop.1.reverse =
        weightedProduct accRev.reverse * contribution.1 := by
  induction fuel generalizing c w i accRev with
  | zero =>
      simp [yunFactors, yunFactorsContribution]
  | succ fuel ih =>
      simp only [yunFactors, yunFactorsContribution]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (i + 1) accRev
        · have htail := ih y (w / y) (i + 1) ({ factor := z, multiplicity := i } :: accRev)
          constructor
          · simpa [y, z, hz] using htail.1
          · have hmul :
                weightedProduct (yunFactors y (w / y) (i + 1) fuel
                    ({ factor := z, multiplicity := i } :: accRev)).1.reverse =
                  weightedProduct accRev.reverse *
                    (pow z i * (yunFactorsContribution y (w / y) (i + 1) fuel).1) := by
              calc
                weightedProduct (yunFactors y (w / y) (i + 1) fuel
                    ({ factor := z, multiplicity := i } :: accRev)).1.reverse
                    = weightedProduct ({ factor := z, multiplicity := i } :: accRev).reverse *
                        (yunFactorsContribution y (w / y) (i + 1) fuel).1 := by
                          simpa [y, z] using htail.2
                _ = (weightedProduct accRev.reverse * pow z i) *
                        (yunFactorsContribution y (w / y) (i + 1) fuel).1 := by
                          rw [weightedProduct_reverse_cons]
                _ = weightedProduct accRev.reverse *
                        (pow z i * (yunFactorsContribution y (w / y) (i + 1) fuel).1) := by
                          exact DensePoly.mul_assoc_poly
                            (weightedProduct accRev.reverse) (pow z i)
                            (yunFactorsContribution y (w / y) (i + 1) fuel).1
            simpa [y, z, hz] using hmul

/--
Product contribution of `squareFreeAuxRev` before it is multiplied into the
caller-provided reverse accumulator.
-/
private def squareFreeAuxRevContribution (f : FpPoly p) (multiplicity : Nat) :
    Nat → FpPoly p
  | 0 => 1
  | fuel + 1 =>
      if f.isZero then
        1
      else
        let df := DensePoly.derivative f
        if df.isZero then
          squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel
        else
          let g := DensePoly.gcd f df
          let c := f / g
          let contribution := yunFactorsContribution c g multiplicity fuel
          if isOne contribution.2 then
            contribution.1
          else
            contribution.1 *
              squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel

private theorem squareFreeAuxRevContribution_pthRoot_correct_pow
    (_hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (_hfuel : f.size < fuel + 1)
    (_hzero : f.isZero = false)
    (_hdf : (DensePoly.derivative f).isZero = true)
    (hroot :
      squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
      pow (pthRoot f) (multiplicity * p) := by
  exact hroot

private theorem derivative_coeff_pred_of_pos_lt
    (f : FpPoly p) {n : Nat} (hn0 : 0 < n) (hn : n < f.size) :
    (DensePoly.derivative f).coeff (n - 1) =
      ((n : Nat) : ZMod64 p) * f.coeff n := by
  unfold DensePoly.derivative
  rw [DensePoly.coeff_ofCoeffs_list]
  have hpred : n - 1 < f.size - 1 := by omega
  have hget :
      (((List.range (f.size - 1)).map
          (fun i => (((i + 1 : Nat) : ZMod64 p) * f.coeff (i + 1)))).getD
        (n - 1) (0 : ZMod64 p)) =
          (((n - 1 + 1 : Nat) : ZMod64 p) * f.coeff (n - 1 + 1)) := by
    simp [List.getD, hpred]
  have hsucc : n - 1 + 1 = n := by omega
  simpa [hsucc] using hget

private theorem zmod64_natCast_ne_zero_of_mod_ne_zero
    (n : Nat) (hn : n % p ≠ 0) :
    ((n : Nat) : ZMod64 p) ≠ 0 := by
  intro hzero
  apply hn
  have hnat := congrArg ZMod64.toNat hzero
  simpa using hnat

private theorem derivative_zero_coeff_non_pmultiple
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (n : Nat)
    (hdf : (DensePoly.derivative f).isZero = true) (hn : n % p ≠ 0) :
    f.coeff n = 0 := by
  by_cases hsize : f.size ≤ n
  · exact DensePoly.coeff_eq_zero_of_size_le f hsize
  · have hnlt : n < f.size := Nat.lt_of_not_ge hsize
    have hn0 : 0 < n := by
      cases n with
      | zero =>
          simp at hn
      | succ n =>
          exact Nat.succ_pos n
    have hderiv_zero_poly : DensePoly.derivative f = 0 :=
      eq_zero_of_isZero_true (DensePoly.derivative f) hdf
    have hderiv_coeff : (DensePoly.derivative f).coeff (n - 1) = 0 := by
      rw [hderiv_zero_poly]
      exact DensePoly.coeff_zero (R := ZMod64 p) (n - 1)
    have hmul :
        ((n : Nat) : ZMod64 p) * f.coeff n = 0 := by
      rw [← derivative_coeff_pred_of_pos_lt f hn0 hnlt]
      exact hderiv_coeff
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hmul with hnzero | hcoeff
    · exact False.elim (zmod64_natCast_ne_zero_of_mod_ne_zero n hn hnzero)
    · exact hcoeff

private theorem pthRoot_frobenius_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (_hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot f) p = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [pthRoot_pow_prime_coeff hp f n]
  by_cases hn : n % p = 0
  · simp [hn]
  · simp [hn, derivative_zero_coeff_non_pmultiple hp f n hdf hn]

private theorem pow_pow_mul
    (f : FpPoly p) (m n : Nat) (_hm : 0 < m) :
    pow (pow f n) m = pow f (m * n) := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_powLinear_mul f m n

private theorem pthRoot_pow_mul_prime_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity : Nat)
    (hmultiplicity : 0 < multiplicity)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot f) (multiplicity * p) = pow f multiplicity := by
  calc
    pow (pthRoot f) (multiplicity * p) =
        pow (pow (pthRoot f) p) multiplicity := by
          exact (pow_pow_mul (pthRoot f) multiplicity p hmultiplicity).symm
    _ = pow f multiplicity := by
          rw [pthRoot_frobenius_of_derivative_zero hp f hzero hdf]

private theorem squareFreeAuxRevContribution_derivative_zero_correct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hroot :
      squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
      pow f multiplicity := by
  calc
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p) := by
          exact squareFreeAuxRevContribution_pthRoot_correct_pow
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf hroot
    _ = pow f multiplicity := by
          exact pthRoot_pow_mul_prime_of_derivative_zero
            hp f multiplicity hmultiplicity hzero hdf

private def squareFreeContributionReachable (f : FpPoly p) : Prop :=
  f.size = 1 → f = 1

private theorem yunFactorsContribution_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false) :
    let g := DensePoly.gcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContribution c g multiplicity fuel
    if isOne contribution.2 then
      contribution.1 = pow f multiplicity
    else
      contribution.1 *
        squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel =
          pow f multiplicity := by
  sorry

private theorem squareFreeAuxRevContribution_correct_pow_of_nonzero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel)
    (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeAuxRevContribution f multiplicity fuel = pow f multiplicity := by
  induction fuel generalizing f multiplicity with
  | zero =>
      omega
  | succ fuel ih =>
      simp only [squareFreeAuxRevContribution]
      simp [hzero]
      by_cases hdf : (DensePoly.derivative f).isZero
      · simpa [hdf] using
          squareFreeAuxRevContribution_derivative_zero_correct
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf (by
              have hmultiplicity_root : 0 < multiplicity * p := by
                have hp_pos : 0 < p := by
                  have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
                  omega
                exact Nat.mul_pos hmultiplicity hp_pos
              have hroot_fuel : (pthRoot f).size < fuel := by
                sorry
              have hroot_zero : (pthRoot f).isZero = false := by
                sorry
              have hroot_reachable : squareFreeContributionReachable (pthRoot f) := by
                sorry
              exact ih (pthRoot f) (multiplicity * p)
                hmultiplicity_root hroot_fuel hroot_zero hroot_reachable)
      · have hdf_false : (DensePoly.derivative f).isZero = false := by
          cases h : (DensePoly.derivative f).isZero <;> simp [h] at hdf ⊢
        simp [hdf_false]
        let g := DensePoly.gcd f (DensePoly.derivative f)
        let c := f / g
        let contribution := yunFactorsContribution c g multiplicity fuel
        have hrec :=
          yunFactorsContribution_reconstruct
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf_false
        by_cases hrepeated : isOne contribution.2
        · simpa [g, c, contribution, hrepeated] using hrec
        · simpa [g, c, contribution, hrepeated] using hrec

/--
Tail-recursive square-free decomposition over `F_p[x]`, accumulating factors
in reverse output order. A derivative-zero branch descends through the formal
`p`-th root and scales multiplicities by `p`.
-/
private def squareFreeAuxRev (f : FpPoly p) (multiplicity : Nat) :
    Nat → List (SquareFreeFactor p) → List (SquareFreeFactor p)
  | 0, accRev => accRev
  | fuel + 1, accRev =>
      if f.isZero then
        accRev
      else
        let df := DensePoly.derivative f
        if df.isZero then
          squareFreeAuxRev (pthRoot f) (multiplicity * p) fuel accRev
        else
          let g := DensePoly.gcd f df
          let c := f / g
          let loop := yunFactors c g multiplicity fuel accRev
          let accRev' := loop.1
          let repeated := loop.2
          if isOne repeated then
            accRev'
          else
            squareFreeAuxRev (pthRoot repeated) (multiplicity * p) fuel accRev'

/--
Recursive square-free decomposition over `F_p[x]`. A derivative-zero branch
descends through the formal `p`-th root and scales multiplicities by `p`.
-/
private def squareFreeAux (f : FpPoly p) (multiplicity : Nat)
    (fuel : Nat) : List (SquareFreeFactor p) :=
  (squareFreeAuxRev f multiplicity fuel []).reverse

private theorem squareFreeAuxRev_reconstruction_invariant
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    weightedProduct (squareFreeAuxRev f multiplicity fuel accRev).reverse =
      weightedProduct accRev.reverse *
        squareFreeAuxRevContribution f multiplicity fuel := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simp [squareFreeAuxRev, squareFreeAuxRevContribution]
  | succ fuel ih =>
      simp only [squareFreeAuxRev, squareFreeAuxRevContribution]
      by_cases hzero : f.isZero
      · simp [hzero]
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactors c g multiplicity fuel accRev
          let contribution := yunFactorsContribution c g multiplicity fuel
          have hloop := yunFactors_reconstruction_invariant c g multiplicity fuel accRev
          have hloop_repeated : loop.2 = contribution.2 := by
            simpa [loop, contribution] using hloop.1
          have hloop_product :
              weightedProduct loop.1.reverse =
                weightedProduct accRev.reverse * contribution.1 := by
            simpa [loop, contribution] using hloop.2
          by_cases hrepeated : isOne loop.2
          · have hcontribution_one : isOne contribution.2 := by
              simpa [hloop_repeated] using hrepeated
            simpa [g, c, loop, contribution, hrepeated, hcontribution_one] using hloop_product
          · have hcontribution_not_one : isOne contribution.2 = false := by
              cases hc : isOne contribution.2
              · exact rfl
              · exfalso
                apply hrepeated
                simpa [hloop_repeated] using hc
            have hrec :
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  weightedProduct loop.1.reverse *
                    squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := by
              exact ih (pthRoot loop.2) (multiplicity * p) loop.1
            have hrec_contribution :
                squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel =
                  squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel := by
              rw [hloop_repeated]
            have hcalc :
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  weightedProduct accRev.reverse *
                    (contribution.1 *
                      squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel) := by
              calc
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse
                    = weightedProduct loop.1.reverse *
                        squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := hrec
                _ = (weightedProduct accRev.reverse * contribution.1) *
                        squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := by
                      rw [hloop_product]
                _ = weightedProduct accRev.reverse *
                        (contribution.1 *
                          squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel) := by
                      exact DensePoly.mul_assoc_poly
                        (weightedProduct accRev.reverse) contribution.1
                        (squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel)
                _ = weightedProduct accRev.reverse *
                        (contribution.1 *
                          squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel) := by
                      rw [hrec_contribution]
            simpa [g, c, loop, contribution, hrepeated, hcontribution_not_one, hloop_repeated]
              using hcalc

private def squareFreeFactorCoprimeRel :
    SquareFreeFactor p → SquareFreeFactor p → Prop :=
  fun a b => DensePoly.gcd a.factor b.factor = 1

private theorem pairwise_append_of_cross
    {α : Type} (r : α → α → Prop) {xs ys : List α} :
    xs.Pairwise r →
    ys.Pairwise r →
    (∀ x ∈ xs, ∀ y ∈ ys, r x y) →
    (xs ++ ys).Pairwise r := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      intro hxs hys hcross
      simp only [List.pairwise_cons] at hxs ⊢
      constructor
      · intro z hz
        rcases List.mem_append.mp hz with hmem | hmem
        · exact hxs.1 z hmem
        · exact hcross x (by simp) z hmem
      · apply ih hxs.2 hys
        intro a ha b hb
        exact hcross a (by simp [ha]) b hb

private theorem yunFactors_reverse_append
    (c w : FpPoly p) (i fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactors c w i fuel accRev).1.reverse =
      accRev.reverse ++ (yunFactors c w i fuel []).1.reverse := by
  induction fuel generalizing c w i accRev with
  | zero =>
      simp [yunFactors]
  | succ fuel ih =>
      simp only [yunFactors]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (i + 1) accRev
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := i }
          have hacc := ih y (w / y) (i + 1) (sf :: accRev)
          have hsingle := ih y (w / y) (i + 1) [sf]
          simpa [y, z, hz, sf] using
            (calc
              (yunFactors y (w / y) (i + 1) fuel (sf :: accRev)).1.reverse
                  = (sf :: accRev).reverse ++
                      (yunFactors y (w / y) (i + 1) fuel []).1.reverse := hacc
              _ = accRev.reverse ++
                    (yunFactors y (w / y) (i + 1) fuel [sf]).1.reverse := by
                  rw [hsingle]
                  simp [List.reverse_cons, List.append_assoc])

private theorem yunFactors_repeated_eq_nil
    (c w : FpPoly p) (i fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactors c w i fuel accRev).2 = (yunFactors c w i fuel []).2 := by
  induction fuel generalizing c w i accRev with
  | zero =>
      simp [yunFactors]
  | succ fuel ih =>
      simp only [yunFactors]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (i + 1) accRev
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := i }
          have hacc := ih y (w / y) (i + 1) (sf :: accRev)
          have hsingle := ih y (w / y) (i + 1) [sf]
          simpa [y, z, hz, sf] using hacc.trans hsingle.symm

private theorem squareFreeAuxRev_reverse_append
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (squareFreeAuxRev f multiplicity fuel accRev).reverse =
      accRev.reverse ++ (squareFreeAuxRev f multiplicity fuel []).reverse := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simp [squareFreeAuxRev]
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simp [hzero]
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactors c g multiplicity fuel accRev
          let loopNil := yunFactors c g multiplicity fuel []
          have hloop_rev :
              loop.1.reverse = accRev.reverse ++ loopNil.1.reverse := by
            simpa [loop, loopNil] using
              yunFactors_reverse_append c g multiplicity fuel accRev
          have hloop_repeated : loop.2 = loopNil.2 := by
            simpa [loop, loopNil] using
              yunFactors_repeated_eq_nil c g multiplicity fuel accRev
          by_cases hrepeated : isOne loop.2
          · have hrepeated_nil : isOne loopNil.2 := by
              simpa [hloop_repeated] using hrepeated
            simpa [g, c, loop, loopNil, hrepeated, hrepeated_nil] using hloop_rev
          · have hrepeated_nil : isOne loopNil.2 = false := by
              cases h : isOne loopNil.2
              · exact rfl
              · exfalso
                apply hrepeated
                simpa [hloop_repeated] using h
            have hrec_loop :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  loop.1.reverse ++
                    (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse := by
              exact ih (pthRoot loop.2) (multiplicity * p) loop.1
            have hrec_nil :
                (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel loopNil.1).reverse =
                  loopNil.1.reverse ++
                    (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse := by
              exact ih (pthRoot loopNil.2) (multiplicity * p) loopNil.1
            have htail :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse =
                  (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse := by
              rw [hloop_repeated]
            simpa [g, c, loop, loopNil, hrepeated, hrepeated_nil] using
              (calc
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse
                    = loop.1.reverse ++
                        (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse :=
                      hrec_loop
                _ = (accRev.reverse ++ loopNil.1.reverse) ++
                        (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse := by
                      rw [hloop_rev]
                _ = accRev.reverse ++
                      (loopNil.1.reverse ++
                        (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse) := by
                      rw [htail]
                      simp [List.append_assoc]
                _ = accRev.reverse ++
                      (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel loopNil.1).reverse := by
                      rw [hrec_nil])

private theorem squareFreeAuxRev_pairwise_coprime_nil_core
    (f : FpPoly p) (multiplicity fuel : Nat) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  sorry

private theorem squareFreeAuxRev_pairwise_coprime_core
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    accRev.reverse.Pairwise squareFreeFactorCoprimeRel →
    (∀ a ∈ accRev.reverse,
      ∀ b ∈ (squareFreeAuxRev f multiplicity fuel []).reverse,
        squareFreeFactorCoprimeRel a b) →
    (squareFreeAuxRev f multiplicity fuel accRev).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  intro hacc hcross
  rw [squareFreeAuxRev_reverse_append f multiplicity fuel accRev]
  apply pairwise_append_of_cross
  · exact hacc
  · exact squareFreeAuxRev_pairwise_coprime_nil_core f multiplicity fuel
  · exact hcross

private theorem squareFreeAuxRev_pairwise_coprime_of_acc
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    accRev.reverse.Pairwise squareFreeFactorCoprimeRel →
    (∀ a ∈ accRev.reverse,
      ∀ b ∈ (squareFreeAuxRev f multiplicity fuel []).reverse,
        squareFreeFactorCoprimeRel a b) →
    (squareFreeAuxRev f multiplicity fuel accRev).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact squareFreeAuxRev_pairwise_coprime_core f multiplicity fuel accRev

private theorem squareFreeAuxRev_pairwise_coprime_nil
    (f : FpPoly p) (multiplicity fuel : Nat) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  apply squareFreeAuxRev_pairwise_coprime_of_acc
  · simp
  · intro a ha
    simp at ha

private def yunFactorsStepsSquareFree (c w : FpPoly p) : Nat → Prop
  | 0 => True
  | fuel + 1 =>
      if isOne c then
        True
      else
        let y := DensePoly.gcd c w
        let z := c / y
        (if isOne z then
          True
        else
          DensePoly.gcd z (DensePoly.derivative z) = 1) ∧
          yunFactorsStepsSquareFree y (w / y) fuel

private theorem yunFactorsStepsSquareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsStepsSquareFree
      (f / DensePoly.gcd f (DensePoly.derivative f))
      (DensePoly.gcd f (DensePoly.derivative f))
      fuel := by
  sorry

private theorem yunFactors_factors_squareFree_of_steps
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hsteps : yunFactorsStepsSquareFree c w fuel)
    (hacc :
      ∀ sf ∈ accRev.reverse, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1) :
    ∀ sf ∈ (yunFactors c w multiplicity fuel accRev).1.reverse,
      DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  induction fuel generalizing c w multiplicity accRev with
  | zero =>
      simpa [yunFactors] using hacc
  | succ fuel ih =>
      simp only [yunFactors]
      by_cases hc : isOne c
      · simpa [hc] using hacc
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        have hsteps_nonone :
            (if isOne z then
              True
            else
              DensePoly.gcd z (DensePoly.derivative z) = 1) ∧
              yunFactorsStepsSquareFree y (w / y) fuel := by
          simpa [yunFactorsStepsSquareFree, hc, y, z] using hsteps
        have hsteps_tail : yunFactorsStepsSquareFree y (w / y) fuel := by
          exact hsteps_nonone.2
        by_cases hz : isOne z
        · simpa [y, z, hz] using
            ih y (w / y) (multiplicity + 1) accRev hsteps_tail hacc
        · have hacc' :
              ∀ sf ∈ ({ factor := z, multiplicity := multiplicity } :: accRev).reverse,
                DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
            intro sf hsf
            rw [List.reverse_cons] at hsf
            rcases List.mem_append.mp hsf with hsf | hsf
            · exact hacc sf hsf
            · simp only [List.mem_singleton] at hsf
              subst sf
              have hstep : DensePoly.gcd z (DensePoly.derivative z) = 1 := by
                simpa [hz] using hsteps_nonone.1
              simpa [z, y] using hstep
          simpa [y, z, hz] using
            ih y (w / y) (multiplicity + 1)
              ({ factor := z, multiplicity := multiplicity } :: accRev) hsteps_tail hacc'

private theorem yunFactors_factors_squareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hacc :
      ∀ sf ∈ accRev.reverse, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1) :
    ∀ sf ∈
        (yunFactors (f / DensePoly.gcd f (DensePoly.derivative f))
          (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel accRev).1.reverse,
      DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  apply yunFactors_factors_squareFree_of_steps
  · exact yunFactorsStepsSquareFree_of_derivative_split hp f fuel hdf
  · exact hacc

private theorem squareFreeAuxRev_factors_squareFree
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hacc :
      ∀ sf ∈ accRev.reverse, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1) :
    ∀ sf ∈ (squareFreeAuxRev f multiplicity fuel accRev).reverse,
      DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simpa [squareFreeAuxRev] using hacc
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simpa [hzero] using hacc
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev hacc
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactors c g multiplicity fuel accRev
          have hloop :
              ∀ sf ∈ loop.1.reverse,
                DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
            simpa [loop, c, g] using
              yunFactors_factors_squareFree_of_derivative_split hp f multiplicity fuel
                accRev hdf hacc
          by_cases hrepeated : isOne loop.2
          · simpa [loop, c, g, hrepeated] using hloop
          · simpa [loop, c, g, hrepeated] using
              ih (pthRoot loop.2) (multiplicity * p) loop.1 hloop

private theorem squareFreeAuxRevContribution_correct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeAuxRevContribution f 1 (f.size + 1) = f := by
  rw [squareFreeAuxRevContribution_correct_pow_of_nonzero hp f 1 (f.size + 1)
    (by omega) (by omega) hzero hreachable]
  exact pow_one f

private theorem squareFreeAux_zero_weightedProduct
    (f : FpPoly p) (hzero : f.isZero = true) :
    weightedProduct (squareFreeAux f 1 (f.size + 1)) = 1 := by
  unfold squareFreeAux
  simp [squareFreeAuxRev, hzero, weightedProduct_nil]

/--
Compute a square-free decomposition by normalizing away the leading scalar and
running Yun's algorithm on the resulting monic polynomial.
-/
def squareFreeDecomposition (hp : Hex.Nat.Prime p) (f : FpPoly p) : SquareFreeDecomposition p :=
  let _ := hp
  let normalized := normalizeMonic f
  let unit := normalized.1
  let monicPart := normalized.2
  let factors := squareFreeAux monicPart 1 (monicPart.size + 1)
  { unit, factors }

private theorem squareFreeAux_weightedProduct_nonzero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f) :
    weightedProduct (squareFreeAux f 1 (f.size + 1)) = f := by
  unfold squareFreeAux
  have hinvariant := squareFreeAuxRev_reconstruction_invariant f 1 (f.size + 1) []
  rw [hinvariant]
  simp [weightedProduct_nil]
  exact squareFreeAuxRevContribution_correct hp f hzero hreachable

private theorem normalizeMonic_squareFreeContributionReachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    squareFreeContributionReachable (normalizeMonic f).2 := by
  intro hsize
  cases hzero : f.isZero
  · rw [normalizeMonic_nonzero f hzero] at hsize ⊢
    change DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f = 1
    change (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size = 1 at hsize
    let unit := DensePoly.leadingCoeff f
    have hunit_ne : unit ≠ 0 := leadingCoeff_ne_zero_of_isZero_false f hzero
    have hinv_ne : unit⁻¹ ≠ 0 :=
      zmod64_inv_ne_zero_of_prime_ne_zero hp hunit_ne
    have hunit_inv : unit⁻¹ * unit = 1 := by
      have h := zmod64_mul_inv_eq_one_of_prime_ne_zero hp hunit_ne
      have hcomm : unit⁻¹ * unit = unit * unit⁻¹ := by grind
      rw [hcomm]
      exact h
    have hscale_size : f.size = 1 := by
      have hpos : 0 < f.size := by
        simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
          Nat.pos_iff_ne_zero] using hzero
      by_cases hle : f.size ≤ 1
      · omega
      · exfalso
        have hgt : 1 < f.size := by omega
        let i := f.size - 1
        have hi_ge : 1 ≤ i := by omega
        have hscaled_zero :
            (DensePoly.scale unit⁻¹ f).coeff i = 0 :=
          DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale unit⁻¹ f) (by
            have hs : (DensePoly.scale unit⁻¹ f).size = 1 := by
              simpa [unit] using hsize
            omega)
        have hscaled_coeff :
            (DensePoly.scale unit⁻¹ f).coeff i = unit⁻¹ * f.coeff i := by
          exact DensePoly.coeff_scale unit⁻¹ f i (zmod64_mul_zero unit⁻¹)
        have hlast : f.coeff i ≠ 0 := by
          simpa [i] using DensePoly.coeff_last_ne_zero_of_pos_size f hpos
        have hmul : unit⁻¹ * f.coeff i = 0 := by
          rw [← hscaled_coeff]
          exact hscaled_zero
        rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hmul with hinv_zero | hcoeff_zero
        · exact hinv_ne hinv_zero
        · exact hlast hcoeff_zero
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        have hcoeff :
            (DensePoly.scale unit⁻¹ f).coeff 0 = unit⁻¹ * f.coeff 0 := by
          exact DensePoly.coeff_scale unit⁻¹ f 0 (zmod64_mul_zero unit⁻¹)
        have hlead : unit = f.coeff 0 := by
          have hlead_last : DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
            unfold DensePoly.leadingCoeff DensePoly.coeff
            rw [Array.back?_eq_getElem?]
            have hidx : f.coeffs.size - 1 < f.coeffs.size := by
              simpa [DensePoly.size] using Nat.sub_one_lt_of_lt (by omega : 0 < f.size)
            simp [Array.getD, DensePoly.size, hidx]
          simpa [unit, hscale_size] using hlead_last
        rw [hcoeff, ← hlead, hunit_inv]
        exact (DensePoly.coeff_C (1 : ZMod64 p) 0).symm
    | succ n =>
        have hcoeff_zero :
            (DensePoly.scale unit⁻¹ f).coeff (n + 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le (DensePoly.scale unit⁻¹ f) (by
            have hs : (DensePoly.scale unit⁻¹ f).size = 1 := by
              simpa [unit] using hsize
            omega)
        rw [hcoeff_zero]
        exact (DensePoly.coeff_C (1 : ZMod64 p) (n + 1)).symm
  · rw [normalizeMonic_zero f hzero] at hsize
    simp at hsize

private theorem normalizeMonic_zero_squareFree_weightedProduct
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : (normalizeMonic f).2.isZero = true) :
    DensePoly.C (normalizeMonic f).1 *
      weightedProduct
        (squareFreeAux (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1)) =
        f := by
  rw [squareFreeAux_zero_weightedProduct (normalizeMonic f).2 hzero]
  have hmonic_zero : (normalizeMonic f).2 = 0 :=
    eq_zero_of_isZero_true (normalizeMonic f).2 hzero
  have hreconstruct := normalizeMonic_reconstruct hp f
  rw [hmonic_zero] at hreconstruct
  simp at hreconstruct
  rw [← hreconstruct]
  rfl

theorem squareFree_pairwise_coprime (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    d.factors.Pairwise (fun a b => DensePoly.gcd a.factor b.factor = 1) := by
  unfold squareFreeDecomposition squareFreeAux
  exact squareFreeAuxRev_pairwise_coprime_nil
    (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1)

theorem squareFree_weightedProduct (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    DensePoly.C d.unit * weightedProduct d.factors = f := by
  dsimp [squareFreeDecomposition]
  by_cases hzero : (normalizeMonic f).2.isZero
  · exact normalizeMonic_zero_squareFree_weightedProduct hp f hzero
  · have hnonzero : (normalizeMonic f).2.isZero = false := by
      cases h : (normalizeMonic f).2.isZero <;> simp [h] at hzero ⊢
    rw [squareFreeAux_weightedProduct_nonzero hp (normalizeMonic f).2 hnonzero
      (normalizeMonic_squareFreeContributionReachable hp f)]
    exact normalizeMonic_reconstruct hp f

theorem squareFree_factors_squareFree (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  unfold squareFreeDecomposition squareFreeAux
  apply squareFreeAuxRev_factors_squareFree hp
  intro sf hsf
  simp at hsf

end FpPoly
end Hex
