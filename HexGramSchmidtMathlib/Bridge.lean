import HexGramSchmidt
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
Bridge scaffolding between `HexGramSchmidt` and Mathlib's `gramSchmidt`.

This module packages the rowwise conversion from Hex's rational-basis
matrices into Mathlib's Euclidean-space view, then states the scaffolded
correspondence theorem surface asserting that the integer-input
Gram-Schmidt basis agrees row-by-row with Mathlib's `gramSchmidt` after
coercing coefficients into `ℝ`.
-/

namespace HexGramSchmidtMathlib

open HexMatrix

namespace Bridge

open Hex

/-- View a dense rational row as a real Euclidean-space vector. -/
def toEuclideanRow (v : Vector Rat m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (V := Fin m → ℝ) fun j => (v.get j : ℝ)

/--
The integer-input rows, coerced into the Euclidean-space family expected
by Mathlib's `gramSchmidt`.
-/
def inputFamily (b : HexMatrix.Matrix Int n m) : Fin n → EuclideanSpace ℝ (Fin m) :=
  fun i => toEuclideanRow (Hex.GramSchmidt.Int.castRow (b.get i))

/--
The scaffolded Hex Gram-Schmidt basis viewed as a family of Euclidean-space
vectors, one row at a time.
-/
noncomputable def basisFamily (b : HexMatrix.Matrix Int n m) : Fin n → EuclideanSpace ℝ (Fin m) :=
  fun i => toEuclideanRow ((Hex.GramSchmidt.Int.basis b).get i)

/--
After coercing coefficients into `ℝ`, the scaffolded Hex basis is intended
to agree with Mathlib's `gramSchmidt` family.
-/
theorem basisFamily_eq_gramSchmidt (b : HexMatrix.Matrix Int n m) :
    basisFamily b = InnerProductSpace.gramSchmidt ℝ (inputFamily b) := by
  sorry

/--
Each scaffolded Hex basis row corresponds to the matching Mathlib
`gramSchmidt` vector on the coerced input family.
-/
theorem basisFamily_apply_eq_gramSchmidt (b : HexMatrix.Matrix Int n m) (i : Fin n) :
    basisFamily b i = InnerProductSpace.gramSchmidt ℝ (inputFamily b) i := by
  simpa using congrFun (basisFamily_eq_gramSchmidt b) i

/--
The coerced Hex basis spans the same real subspace as the coerced input
rows, matching Mathlib's span-preservation theorem for `gramSchmidt`.
-/
theorem span_basisFamily_eq_span_inputFamily (b : HexMatrix.Matrix Int n m) :
    Submodule.span ℝ (Set.range (basisFamily b)) =
      Submodule.span ℝ (Set.range (inputFamily b)) := by
  simpa [basisFamily_eq_gramSchmidt b] using
    (InnerProductSpace.span_gramSchmidt (𝕜 := ℝ) (f := inputFamily b))

end Bridge

end HexGramSchmidtMathlib
