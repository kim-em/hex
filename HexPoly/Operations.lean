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
  ofCoeffs <| (List.range p.size).map (fun i => c * p.coeff i) |>.toArray

/-- Multiply by `x^n`. -/
def shift (n : Nat) (p : DensePoly R) : DensePoly R :=
  if p.isZero then 0 else
    ofCoeffs <| ((List.replicate n (Zero.zero : R)) ++ p.toArray.toList).toArray

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
