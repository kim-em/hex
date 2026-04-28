import HexMatrixMathlib.Basic
import HexMatrix.RREF
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Rank, row-span, and nullspace bridge theorems for `hex-matrix-mathlib`.

This module converts the executable `Hex.Matrix` row-reduction surface into
Mathlib's function-based matrix model, then states the Phase 1 bridge theorems
relating computed rank, span membership, and nullspace bases to Mathlib's
noncomputable linear-algebra definitions.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n m : Nat}

/-- Convert an executable `Vector` into Mathlib's function representation. -/
def vectorEquiv : Vector R n ≃ (Fin n → R) where
  toFun := fun v i => v[i]
  invFun := Vector.ofFn
  left_inv := by
    intro v
    ext i
    simp
  right_inv := by
    intro f
    funext i
    simp

@[simp] theorem vectorEquiv_apply (v : Vector R n) (i : Fin n) :
    vectorEquiv v i = v[i] :=
  rfl

@[simp] theorem vectorEquiv_symm_apply (f : Fin n → R) (i : Fin n) :
    (vectorEquiv.symm f)[i] = f i := by
  simp [vectorEquiv]

@[simp] theorem matrixEquiv_row (M : Hex.Matrix R n m) (i : Fin n) :
    _root_.Matrix.row (matrixEquiv M) i = vectorEquiv (Hex.Matrix.row M i) := by
  funext j
  simp [Hex.Matrix.row]

theorem rank_eq [Field R] (M : Hex.Matrix R n m)
    (D : Hex.Matrix.RowEchelonData R n m) (E : Hex.Matrix.IsEchelonForm M D) :
    D.rank = _root_.Matrix.rank (matrixEquiv M) := by
  sorry

theorem spanCoeffs_eq_linearCombination [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsEchelonForm M D) (v : Vector R m) (c : Vector R n) :
    E.spanCoeffs v = some c →
      vectorEquiv v =
        Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c) := by
  sorry

theorem spanContains_iff_mem_span [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsEchelonForm M D) (v : Vector R m) :
    E.spanContains v = true ↔
      vectorEquiv v ∈ Submodule.span R (Set.range (_root_.Matrix.row (matrixEquiv M))) := by
  sorry

theorem nullspace_mem_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRREF M D) (k : Fin (m - D.rank)) :
    vectorEquiv (E.nullspace.get k) ∈
      LinearMap.ker ((_root_.Matrix.mulVecLin (matrixEquiv M))) := by
  sorry

theorem nullspace_span_eq_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRREF M D) :
    Submodule.span R (Set.range fun k : Fin (m - D.rank) => vectorEquiv (E.nullspace.get k)) =
      LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv M)) := by
  sorry

end HexMatrixMathlib
