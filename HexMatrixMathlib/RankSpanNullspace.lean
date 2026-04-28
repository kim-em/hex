import HexMatrix
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Rank, row-span, and nullspace bridge theorems for `hex-matrix-mathlib`.

This module converts the executable `Hex.Matrix` row-reduction surface into
Mathlib's function-based matrix model, then states the Phase 1 bridge theorems
relating computed rank, span membership, and nullspace bases to Mathlib's
noncomputable linear-algebra definitions.
-/

namespace Hex
namespace MatrixMathlib

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

/-- Convert an executable `Hex.Matrix` into Mathlib's matrix representation. -/
def matrixEquiv : Hex.Matrix R n m ≃ _root_.Matrix (Fin n) (Fin m) R where
  toFun := fun M i j => M[i][j]
  invFun := fun A => Vector.ofFn fun i => Vector.ofFn fun j => A i j
  left_inv := by
    intro M
    ext i j
    simp
  right_inv := by
    intro A
    funext i j
    simp

@[simp] theorem vectorEquiv_apply (v : Vector R n) (i : Fin n) :
    vectorEquiv v i = v[i] :=
  rfl

@[simp] theorem vectorEquiv_symm_apply (f : Fin n → R) (i : Fin n) :
    (vectorEquiv.symm f)[i] = f i := by
  simpa [vectorEquiv] using Vector.get_ofFn f i

@[simp] theorem matrixEquiv_apply (M : Hex.Matrix R n m) (i : Fin n) (j : Fin m) :
    matrixEquiv M i j = M[i][j] :=
  rfl

@[simp] theorem matrixEquiv_symm_apply
    (A : _root_.Matrix (Fin n) (Fin m) R) (i : Fin n) (j : Fin m) :
    (matrixEquiv.symm A)[i][j] = A i j := by
  simpa [matrixEquiv] using Vector.get_ofFn (f := fun i => Vector.ofFn fun j => A i j) i ▸
    Vector.get_ofFn (f := fun j => A i j) j

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

end MatrixMathlib
end Hex
