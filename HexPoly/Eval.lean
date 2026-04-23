import HexPoly.Division

/-!
Dense polynomial evaluation scaffolding.

This module adds Horner-style evaluation and composition together with
the formal derivative operation for dense polynomials.
-/
namespace HexPoly

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- The constant polynomial with coefficient `a`. -/
private def constant (a : R) : _root_.HexPoly.DensePoly R :=
  ofArray #[a]

/-- Repeated addition by a natural-number coefficient. -/
private def natScale [Add R] (n : Nat) (a : R) : R :=
  Nat.rec (motive := fun _ => R) 0 (fun _ acc => acc + a) n

/-- Horner evaluation for coefficients in ascending degree order. -/
private def evalList [Add R] [Mul R] (x : R) : List R → R
  | [] => 0
  | a :: as => a + x * evalList x as

/-- Horner-style polynomial composition for ascending coefficient lists. -/
private def composeList [Add R] [Mul R]
    (q : _root_.HexPoly.DensePoly R) : List R → _root_.HexPoly.DensePoly R
  | [] => 0
  | a :: as => constant a + q * composeList q as

/--
Derivative coefficients for an ascending coefficient list.

The accumulator index tracks the source degree of the current head coefficient.
-/
private def derivativeCoeffsAux [Add R] : Nat → List R → List R
  | _, [] => []
  | 0, _ :: as => derivativeCoeffsAux 1 as
  | n + 1, a :: as => natScale (n + 1) a :: derivativeCoeffsAux (n + 2) as

/-- Evaluate a dense polynomial at `x` using Horner's method. -/
def eval [Add R] [Mul R] (p : _root_.HexPoly.DensePoly R) (x : R) : R :=
  evalList x p.coeffs.toList

/-- Compose dense polynomials using the Horner recursion on coefficients. -/
def compose [Add R] [Mul R]
    (p q : _root_.HexPoly.DensePoly R) : _root_.HexPoly.DensePoly R :=
  composeList q p.coeffs.toList

/-- The formal derivative of a dense polynomial. -/
def derivative [Add R] (p : _root_.HexPoly.DensePoly R) : _root_.HexPoly.DensePoly R :=
  ofArray (derivativeCoeffsAux 0 p.coeffs.toList |>.toArray)

/-- Evaluating the zero polynomial returns zero. -/
theorem eval_zero [Add R] [Mul R] (x : R) :
    eval (R := R) 0 x = 0 := by
  sorry

/-- Composing the zero polynomial with any polynomial yields zero. -/
theorem zero_compose [Add R] [Mul R] (p : _root_.HexPoly.DensePoly R) :
    compose (R := R) 0 p = 0 := by
  sorry

/-- The derivative of the zero polynomial is zero. -/
theorem derivative_zero [Add R] :
    derivative (R := R) 0 = 0 := by
  sorry

end DensePoly
end HexPoly
