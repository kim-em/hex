import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Ring.InjSurj
import HexPoly

/-!
Bridge scaffolding between `HexPoly.DensePoly` and Mathlib polynomials.

This module defines the first `HexPolyMathlib` API slice: an explicit
conversion pair between dense array-backed polynomials and Mathlib's
`Polynomial`, together with the scaffolded ring equivalence built from
those maps.
-/

namespace HexPolyMathlib

open Polynomial

universe u

noncomputable section

namespace DensePoly

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- Interpret an ascending coefficient list as a polynomial. -/
private def toPolynomialList : List R → R[X]
  | [] => 0
  | a :: as => C a + X * toPolynomialList as

/-- Convert a dense polynomial into Mathlib's `Polynomial`. -/
def toPolynomial (p : HexPoly.DensePoly R) : R[X] :=
  toPolynomialList p.coeffs.toList

/--
Convert a Mathlib polynomial into the dense array-backed representation by
reading coefficients from degree `0` through `natDegree`.
-/
def ofPolynomial (p : R[X]) : HexPoly.DensePoly R :=
  HexPoly.DensePoly.ofArray <|
    ((List.range p.degree.succ).map p.coeff).toArray

/-- The dense polynomial constant `1`. -/
instance : One (HexPoly.DensePoly R) where
  one := HexPoly.DensePoly.ofArray #[1]

/-- Negation is coefficientwise, followed by normalization. -/
def neg (p : HexPoly.DensePoly R) : HexPoly.DensePoly R :=
  HexPoly.DensePoly.ofArray (p.coeffs.map Neg.neg)

instance : Neg (HexPoly.DensePoly R) where
  neg := neg

/-- Natural-number scalar multiplication is coefficientwise. -/
instance : SMul ℕ (HexPoly.DensePoly R) where
  smul n p := HexPoly.DensePoly.ofArray (p.coeffs.map (n • ·))

/-- Integer scalar multiplication is coefficientwise. -/
instance : SMul ℤ (HexPoly.DensePoly R) where
  smul z p := HexPoly.DensePoly.ofArray (p.coeffs.map (z • ·))

instance : NatCast (HexPoly.DensePoly R) where
  natCast n := HexPoly.DensePoly.ofArray #[n]

instance : IntCast (HexPoly.DensePoly R) where
  intCast z := HexPoly.DensePoly.ofArray #[z]

instance : Pow (HexPoly.DensePoly R) Nat where
  pow p n := npowRec n p

theorem ofPolynomial_toPolynomial (p : HexPoly.DensePoly R) :
    ofPolynomial (toPolynomial p) = p := by
  sorry

theorem toPolynomial_ofPolynomial (p : R[X]) :
    toPolynomial (ofPolynomial p) = p := by
  sorry

theorem toPolynomial_injective :
    Function.Injective (toPolynomial (R := R)) :=
  Function.LeftInverse.injective (ofPolynomial_toPolynomial (R := R))

@[simp] theorem toPolynomial_zero :
    toPolynomial (0 : HexPoly.DensePoly R) = 0 := by
  sorry

@[simp] theorem toPolynomial_one :
    toPolynomial (1 : HexPoly.DensePoly R) = 1 := by
  sorry

@[simp] theorem toPolynomial_add (p q : HexPoly.DensePoly R) :
    toPolynomial (p + q) = toPolynomial p + toPolynomial q := by
  sorry

@[simp] theorem toPolynomial_mul (p q : HexPoly.DensePoly R) :
    toPolynomial (p * q) = toPolynomial p * toPolynomial q := by
  sorry

@[simp] theorem toPolynomial_neg (p : HexPoly.DensePoly R) :
    toPolynomial (-p) = -toPolynomial p := by
  sorry

@[simp] theorem toPolynomial_sub (p q : HexPoly.DensePoly R) :
    toPolynomial (p - q) = toPolynomial p - toPolynomial q := by
  sorry

@[simp] theorem toPolynomial_pow (p : HexPoly.DensePoly R) (n : Nat) :
    toPolynomial (p ^ n) = toPolynomial p ^ n := by
  sorry

instance : Semiring (HexPoly.DensePoly R) :=
  Function.Injective.semiring
    (toPolynomial (R := R))
    toPolynomial_injective
    toPolynomial_zero
    toPolynomial_one
    toPolynomial_add
    toPolynomial_mul
    (fun n p => by
      sorry)
    toPolynomial_pow
    (fun n => by
      sorry)

instance : Ring (HexPoly.DensePoly R) :=
  Function.Injective.ring
    (toPolynomial (R := R))
    toPolynomial_injective
    toPolynomial_zero
    toPolynomial_one
    toPolynomial_add
    toPolynomial_mul
    toPolynomial_neg
    toPolynomial_sub
    (fun n p => by
      sorry)
    (fun z p => by
      sorry)
    toPolynomial_pow
    (fun n => by
      sorry)
    (fun z => by
      sorry)

instance : CommRing (HexPoly.DensePoly R) :=
  Function.Injective.commRing
    (toPolynomial (R := R))
    toPolynomial_injective
    toPolynomial_zero
    toPolynomial_one
    toPolynomial_add
    toPolynomial_mul
    toPolynomial_neg
    toPolynomial_sub
    (fun n p => by
      sorry)
    (fun z p => by
      sorry)
    toPolynomial_pow
    (fun n => by
      sorry)
    (fun z => by
      sorry)

/-- Scaffolded ring equivalence between dense polynomials and Mathlib polynomials. -/
def equiv : HexPoly.DensePoly R ≃+* R[X] where
  toFun := toPolynomial
  invFun := ofPolynomial
  left_inv := ofPolynomial_toPolynomial
  right_inv := toPolynomial_ofPolynomial
  map_mul' := toPolynomial_mul
  map_add' := toPolynomial_add

end DensePoly
end
end HexPolyMathlib
