import HexPoly.Dense

/-!
Executable arithmetic operations for dense array-backed polynomials.

This module implements executable `DensePoly` operations: addition,
subtraction, schoolbook multiplication, Horner evaluation, composition,
and derivative. All constructors route through `ofCoeffs`, so results are
re-normalized automatically.
-/
namespace Hex

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- Repeated addition by a natural number, implemented without extra algebra imports. -/
private def natScale [Add R] (n : Nat) (x : R) : R :=
  Nat.rec (Zero.zero : R) (fun _ acc => acc + x) n

/-- Multiply every coefficient by `c`. -/
def scale [Mul R] (c : R) (p : DensePoly R) : DensePoly R :=
  ofCoeffs <| p.toArray.toList.map (fun a => c * a) |>.toArray

/-- Multiply by `x^n`. -/
def shift (n : Nat) (p : DensePoly R) : DensePoly R :=
  if p.isZero then 0 else
    ofCoeffs <| ((List.replicate n (Zero.zero : R)) ++ p.toArray.toList).toArray

omit [DecidableEq R] in
private theorem list_getD_map_mul_zero [Mul R] (c : R) (coeffs : List R) (n : Nat)
    (hzero : c * (Zero.zero : R) = (Zero.zero : R)) :
    (coeffs.map fun a => c * a).getD n (Zero.zero : R) =
      c * coeffs.getD n (Zero.zero : R) := by
  induction coeffs generalizing n with
  | nil =>
      simp [hzero]
  | cons a as ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simpa using ih n

omit [DecidableEq R] in
private theorem list_getD_replicate_append_zero (n k : Nat) (coeffs : List R) :
    (List.replicate n (Zero.zero : R) ++ coeffs).getD k (Zero.zero : R) =
      if k < n then (Zero.zero : R) else coeffs.getD (k - n) (Zero.zero : R) := by
  induction n generalizing k with
  | zero =>
      simp
  | succ n ih =>
      cases k with
      | zero =>
          simp [List.replicate]
      | succ k =>
          simpa [Nat.succ_sub_succ_eq_sub] using ih k

theorem coeff_scale [Mul R] (c : R) (p : DensePoly R) (n : Nat)
    (hzero : c * (Zero.zero : R) = (Zero.zero : R)) :
    (scale c p).coeff n = c * p.coeff n := by
  unfold scale
  rw [coeff_ofCoeffs_list]
  simpa [coeff] using list_getD_map_mul_zero (R := R) c p.toArray.toList n hzero

theorem coeff_shift (n : Nat) (p : DensePoly R) (k : Nat) :
    (shift n p).coeff k =
      if k < n then (Zero.zero : R) else p.coeff (k - n) := by
  unfold shift
  by_cases hp : p.isZero
  · have hsize : p.size = 0 := by
      simp [isZero] at hp
      simpa [size] using hp
    by_cases hk : k < n
    · simp [hp, hk]
      change (0 : DensePoly R).coeff k = (Zero.zero : R)
      exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)
    · have hzero : p.coeff (k - n) = (Zero.zero : R) := by
        exact coeff_eq_zero_of_size_le p (by omega)
      simp [hp, hk, hzero]
      change (0 : DensePoly R).coeff k = (Zero.zero : R)
      exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)
  · rw [if_neg hp]
    rw [coeff_ofCoeffs_list]
    simpa [coeff] using list_getD_replicate_append_zero (R := R) n k p.toArray.toList

theorem coeff_shift_scale [Mul R] (i : Nat) (c : R) (p : DensePoly R) (k : Nat)
    (hzero : c * (Zero.zero : R) = (Zero.zero : R)) :
    (shift i (scale c p)).coeff k =
      if k < i then (Zero.zero : R) else c * p.coeff (k - i) := by
  rw [coeff_shift]
  by_cases hk : k < i
  · simp [hk]
  · simp [hk, coeff_scale, hzero]

/-- Add two dense polynomials coefficientwise. -/
def add [Add R] (p q : DensePoly R) : DensePoly R :=
  let size := max p.size q.size
  ofCoeffs <| (List.range size).map (fun i => p.coeff i + q.coeff i) |>.toArray

instance [Add R] : Add (DensePoly R) where
  add := add

/-- Subtract two dense polynomials coefficientwise. -/
def sub [Sub R] (p q : DensePoly R) : DensePoly R :=
  let size := max p.size q.size
  ofCoeffs <| (List.range size).map (fun i => p.coeff i - q.coeff i) |>.toArray

instance [Sub R] : Sub (DensePoly R) where
  sub := sub

/-- Coefficientwise additive inverse, expressed through executable subtraction. -/
def neg [Sub R] (p : DensePoly R) : DensePoly R :=
  0 - p

instance [Sub R] : Neg (DensePoly R) where
  neg := neg

/-- Schoolbook dense polynomial multiplication. -/
def mul [Add R] [Mul R] (p q : DensePoly R) : DensePoly R :=
  (List.range p.size).foldl
    (fun acc i => acc + (shift i <| scale (p.coeff i) q))
    (0 : DensePoly R)

instance [Add R] [Mul R] : Mul (DensePoly R) where
  mul := mul

/-- Evaluate a polynomial using Horner's method. -/
def eval [Add R] [Mul R] (p : DensePoly R) (x : R) : R :=
  p.toArray.toList.reverse.foldl (fun acc coeff => acc * x + coeff) (Zero.zero : R)

/-- Compose polynomials using Horner's method. -/
def compose [Add R] [Mul R] (p q : DensePoly R) : DensePoly R :=
  p.toArray.toList.reverse.foldl (fun acc coeff => acc * q + C coeff) (0 : DensePoly R)

/-- Formal derivative. The coefficient of `x^i` becomes `(i + 1) * a_(i+1)`. -/
def derivative [Add R] (p : DensePoly R) : DensePoly R :=
  ofCoeffs <|
    (List.range (p.size - 1)).map (fun i => natScale (i + 1) <| p.coeff (i + 1)) |>.toArray

theorem coeff_add [Add R] (p q : DensePoly R) (n : Nat) :
    (p + q).coeff n = (p.coeff n + q.coeff n) := by
  sorry

theorem coeff_sub [Sub R] (p q : DensePoly R) (n : Nat) :
    (p - q).coeff n = (p.coeff n - q.coeff n) := by
  sorry

@[simp] theorem coeff_zero (n : Nat) :
    (0 : DensePoly R).coeff n = (0 : R) := by
  exact coeff_eq_zero_of_size_le (0 : DensePoly R) (by simp)

theorem coeff_neg [Sub R] (p : DensePoly R) (n : Nat) :
    (-p).coeff n = ((0 : R) - p.coeff n) := by
  change (neg p).coeff n = ((0 : R) - p.coeff n)
  simp [neg, coeff_sub]

theorem eval_zero [Add R] [Mul R] (x : R) :
    eval (0 : DensePoly R) x = 0 := by
  sorry

theorem eval_C [Add R] [Mul R] (c x : R) :
    eval (C c) x = c := by
  sorry

theorem derivative_zero [Add R] :
    derivative (0 : DensePoly R) = 0 := by
  sorry

end DensePoly
end Hex
