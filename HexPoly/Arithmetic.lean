import HexPoly.DensePoly

/-!
Dense polynomial arithmetic scaffolding.

This module exposes the basic arithmetic operations on dense
polynomials: coefficientwise addition and subtraction together with
schoolbook multiplication.
-/
namespace HexPoly

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/--
Zip two coefficient lists with zero-padding so arithmetic can proceed
uniformly across different supports.
-/
private def zipWithZero (f : R → R → R) : List R → List R → List R
  | [], [] => []
  | a :: as, [] => f a (default : R) :: zipWithZero f as []
  | [], b :: bs => f (default : R) b :: zipWithZero f [] bs
  | a :: as, b :: bs => f a b :: zipWithZero f as bs

/-- Multiply every coefficient in a list by a fixed scalar. -/
private def scaleList [Mul R] (a : R) : List R → List R
  | [] => []
  | b :: bs => (a * b) :: scaleList a bs

/--
Schoolbook multiplication for coefficient lists stored in ascending degree
order.
-/
private def mulList [Add R] [Mul R] : List R → List R → List R
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, bs =>
      zipWithZero (· + ·) (scaleList a bs) ((default : R) :: mulList as bs)

/-- Raw coefficient array for polynomial addition before normalization. -/
def addCoeffs [Add R] (coeffs₁ coeffs₂ : Array R) : Array R :=
  (zipWithZero (· + ·) coeffs₁.toList coeffs₂.toList).toArray

/-- Raw coefficient array for polynomial subtraction before normalization. -/
def subCoeffs [Sub R] (coeffs₁ coeffs₂ : Array R) : Array R :=
  (zipWithZero (· - ·) coeffs₁.toList coeffs₂.toList).toArray

/-- Raw coefficient array for polynomial multiplication before normalization. -/
def mulCoeffs [Add R] [Mul R] (coeffs₁ coeffs₂ : Array R) : Array R :=
  (mulList coeffs₁.toList coeffs₂.toList).toArray

/-- Add dense polynomials and renormalize the resulting coefficient array. -/
def add [Add R] (p q : _root_.HexPoly.DensePoly R) : _root_.HexPoly.DensePoly R :=
  ofArray (addCoeffs p.coeffs q.coeffs)

/-- Subtract dense polynomials and renormalize the resulting coefficient array. -/
def sub [Sub R] (p q : _root_.HexPoly.DensePoly R) : _root_.HexPoly.DensePoly R :=
  ofArray (subCoeffs p.coeffs q.coeffs)

/-- Multiply dense polynomials using schoolbook convolution. -/
def mul [Add R] [Mul R] (p q : _root_.HexPoly.DensePoly R) : _root_.HexPoly.DensePoly R :=
  ofArray (mulCoeffs p.coeffs q.coeffs)

instance [Add R] : Add (_root_.HexPoly.DensePoly R) where
  add := DensePoly.add

instance [Sub R] : Sub (_root_.HexPoly.DensePoly R) where
  sub := DensePoly.sub

instance [Add R] [Mul R] : Mul (_root_.HexPoly.DensePoly R) where
  mul := DensePoly.mul

end DensePoly
end HexPoly
