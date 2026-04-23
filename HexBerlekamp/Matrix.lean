import HexMatrix
import HexPolyFp.Frobenius

/-!
Executable Berlekamp-matrix scaffolding for `HexBerlekamp`.

This module introduces the first public algorithmic surface for the
library: the Berlekamp matrix `Q_f` recording the Frobenius map
`h ↦ h^p mod f` in the basis `{1, X, ..., X^(n - 1)}`. The executable
definitions stay close to the polynomial-level Frobenius scaffold from
`HexPolyFp`, while theorem declarations pin down the intended basis and
reduced-remainder interpretation for later phases.
-/

namespace HexBerlekamp

open HexModArith
open HexMatrix

variable {p : Nat} [NeZero p]

/-- The `j`-th standard basis polynomial `X^j` over `F_p`. -/
def basisPolynomial (j : Nat) : HexPolyFp.FpPoly p :=
  HexPolyFp.FpPoly.monomial 1 j

/--
The Frobenius image of the `j`-th basis polynomial modulo `f`.

This is the polynomial whose coefficients populate column `j` of the
Berlekamp matrix.
-/
def frobeniusBasisImage (f : HexPolyFp.FpPoly p) (j : Nat) : HexPolyFp.FpPoly p :=
  HexPolyFp.FpPoly.frobeniusModMonic (basisPolynomial (p := p) j) f

/-- Column `j` of the Berlekamp matrix, read as basis coefficients. -/
def berlekampColumn (f : HexPolyFp.FpPoly p) (j : Fin f.degree) :
    Vector (ZMod64 p) f.degree :=
  Vector.ofFn (fun i => (frobeniusBasisImage (p := p) f j.val).coeff i.val)

/--
Executable Berlekamp matrix `Q_f` for the Frobenius action modulo `f`.

Rows and columns are both indexed by `Fin f.degree`; the `(i,j)` entry is
the coefficient of `X^i` in `(X^j)^p mod f`.
-/
def berlekampMatrix (f : HexPolyFp.FpPoly p) : Matrix (ZMod64 p) f.degree f.degree :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => (berlekampColumn (p := p) f j)[i]))

/-- The chosen basis polynomials are exactly the monomials `X^j`. -/
theorem basisPolynomial_eq_monomial (j : Nat) :
    basisPolynomial (p := p) j = HexPolyFp.FpPoly.monomial 1 j := by
  rfl

/-- The Frobenius basis-image helper is the modular Frobenius of `X^j`. -/
theorem frobeniusBasisImage_eq (f : HexPolyFp.FpPoly p) (j : Nat) :
    frobeniusBasisImage (p := p) f j =
      HexPolyFp.FpPoly.frobeniusModMonic (basisPolynomial (p := p) j) f := by
  rfl

/-- Berlekamp-matrix columns are coefficient vectors of Frobenius images. -/
theorem berlekampColumn_apply (f : HexPolyFp.FpPoly p) (j : Fin f.degree) (i : Fin f.degree) :
    (berlekampColumn (p := p) f j)[i] =
      (frobeniusBasisImage (p := p) f j.val).coeff i.val := by
  simp [berlekampColumn]

/-- Each Berlekamp-matrix entry records a basis coefficient of a Frobenius image. -/
theorem berlekampMatrix_apply (f : HexPolyFp.FpPoly p) (i j : Fin f.degree) :
    (berlekampMatrix (p := p) f)[i][j] =
      (frobeniusBasisImage (p := p) f j.val).coeff i.val := by
  simp [berlekampMatrix, berlekampColumn]

/--
For nonzero monic moduli, each Frobenius basis image is already reduced
to degree `< deg f` (or is zero).
-/
theorem frobeniusBasisImage_degree_lt (f : HexPolyFp.FpPoly p) (j : Nat)
    (hmonic : HexPoly.DensePoly.Monic f) (hneq : f ≠ 0) :
    (frobeniusBasisImage (p := p) f j).natDegree? = none ∨
      (frobeniusBasisImage (p := p) f j).degree < f.degree := by
  simpa [frobeniusBasisImage] using
    HexPolyFp.FpPoly.frobeniusModMonic_degree_lt
      (f := basisPolynomial (p := p) j) (modulus := f) hmonic hneq

/--
Column `j` of `Q_f` is the coordinate vector of the Frobenius image of
the basis element `X^j` modulo `f`.
-/
theorem berlekampMatrix_column_spec (f : HexPolyFp.FpPoly p) (j : Fin f.degree) :
    ∀ i : Fin f.degree,
      (berlekampMatrix (p := p) f)[i][j] =
        (frobeniusBasisImage (p := p) f j.val).coeff i.val := by
  intro i
  simpa using berlekampMatrix_apply (p := p) f i j

end HexBerlekamp
