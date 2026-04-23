import Mathlib.LinearAlgebra.Matrix.ToLin
import HexMatrix.Nullspace
import HexMatrixMathlib.MatrixEquiv

/-!
Bridge scaffolding between Hex's executable nullspace basis and Mathlib's
kernel submodule for dense matrices.

This module states the Phase 1 correspondence theorem identifying the span of
Hex's computed nullspace basis vectors with `LinearMap.ker` after transport by
`vectorEquiv` and `matrixEquiv`.
-/

namespace HexMatrixMathlib

universe u

variable {R : Type u} [Field R] {n m : Nat}

/--
Hex's computed nullspace basis spans Mathlib's kernel after transport along
`vectorEquiv` and `matrixEquiv`.
-/
theorem nullspace_span_eq_ker (M : HexMatrix.Matrix R n m) :
    Submodule.span R
        (Set.range fun k : Fin (m - (HexMatrix.rref M).rank) =>
          vectorEquiv R m ((HexMatrix.Matrix.nullspace M)[k])) =
      LinearMap.ker (Matrix.mulVecLin (matrixEquiv R n m M)) := by
  sorry

end HexMatrixMathlib
