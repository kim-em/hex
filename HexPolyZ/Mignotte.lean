import HexPolyZ.Basic

/-!
Executable Mignotte-bound helpers for `hex-poly-z`.

This module packages the integer computations that appear in the classical
Mignotte coefficient bound: binomial coefficients together with the Euclidean
norm upper bound of the ambient polynomial's coefficient vector. The
mathematical proof that these quantities bound factors lives in
`HexPolyZMathlib`.
-/
namespace Hex

namespace ZPoly

/-- Executable binomial coefficients for the Mignotte bound. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- A simple floor square-root on naturals, implemented by descending search. -/
private def sqrtAux (n : Nat) : Nat → Nat
  | 0 => 0
  | guess + 1 =>
      if (guess + 1) * (guess + 1) ≤ n then
        guess + 1
      else
        sqrtAux n guess

/-- The floor of the square root of `n`. -/
def floorSqrt (n : Nat) : Nat :=
  sqrtAux n n

/-- The least natural number whose square is at least `n`. -/
def ceilSqrt (n : Nat) : Nat :=
  let r := floorSqrt n
  if r * r = n then
    r
  else
    r + 1

/-- The squared Euclidean norm of the coefficient vector of `f`. -/
def coeffNormSq (f : ZPoly) : Nat :=
  (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0

/-- A conservative natural-number upper bound on the Euclidean norm of the
coefficient vector of `f`. -/
def coeffL2NormBound (f : ZPoly) : Nat :=
  ceilSqrt (coeffNormSq f)

/-- The executable Mignotte bound for the `j`-th coefficient of a degree-`k`
factor of `f`, using the conservative `coeffL2NormBound`. -/
def mignotteCoeffBound (f : ZPoly) (k j : Nat) : Nat :=
  binom k j * coeffL2NormBound f

@[simp] theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem binom_zero_succ (k : Nat) : binom 0 (k + 1) = 0 := rfl

theorem binom_eq_zero_of_lt : ∀ {n k : Nat}, n < k → binom n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, hk => by
      have hk' : n < k := Nat.lt_of_succ_lt_succ hk
      have hk'' : n < k + 1 := Nat.lt_of_succ_lt hk
      simp [binom, binom_eq_zero_of_lt hk', binom_eq_zero_of_lt hk'']

@[simp] theorem floorSqrt_zero : floorSqrt 0 = 0 := by
  rfl

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

theorem coeffNormSq_eq_sum (f : ZPoly) :
    coeffNormSq f =
      (List.range f.size).foldl (fun acc i => acc + (f.coeff i).natAbs ^ 2) 0 := rfl

theorem coeffL2NormBound_eq_ceilSqrt_coeffNormSq (f : ZPoly) :
    coeffL2NormBound f = ceilSqrt (coeffNormSq f) := rfl

theorem mignotteCoeffBound_eq (f : ZPoly) (k j : Nat) :
    mignotteCoeffBound f k j = binom k j * coeffL2NormBound f := rfl

@[simp] theorem coeffNormSq_zero : coeffNormSq (0 : ZPoly) = 0 := by
  rfl

@[simp] theorem coeffL2NormBound_zero : coeffL2NormBound (0 : ZPoly) = 0 := by
  simp [coeffL2NormBound]

@[simp] theorem mignotteCoeffBound_zero (k j : Nat) :
    mignotteCoeffBound (0 : ZPoly) k j = 0 := by
  simp [mignotteCoeffBound]

theorem mignotteCoeffBound_eq_zero_of_lt (f : ZPoly) (k j : Nat) (h : k < j) :
    mignotteCoeffBound f k j = 0 := by
  simp [mignotteCoeffBound, binom_eq_zero_of_lt h]

end ZPoly
end Hex
