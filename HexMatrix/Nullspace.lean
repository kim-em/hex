import HexMatrix.Rref

/-!
Nullspace scaffolding for dense matrices.

This module introduces the Phase 1 API surface for constructing a
nullspace basis from existing reduced row-echelon data.
-/
namespace HexMatrix

universe u

open Lean.Grind

namespace Matrix

variable {R : Type u}

/--
Evaluate a dense matrix against a column vector.

This is the standard matrix-times-column-vector pairing used by the
nullspace scaffold.
-/
def mulVecRight [Zero R] [Add R] [Mul R] (M : Matrix R n m) (v : Vector R m) : Vector R n :=
  Vector.ofFn fun i => dot M[i] v

instance instHMulColVector [Zero R] [Add R] [Mul R] :
    HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVecRight

end Matrix

namespace IsRREF

variable {R : Type u} [Zero R] [One R] [Add R] [Mul R] [Neg R]
variable {n m : Nat} {M : Matrix R n m} {D : RowEchelonData R n m}

private def pivotRow? (D : RowEchelonData R n m) (j : Fin m) : Option (Fin D.rank) :=
  (List.finRange D.rank).foldr (fun i acc => if D.pivotCols[i] = j then some i else acc) none

/--
Temporary Phase 1 scaffold for the nullspace basis matrix extracted from
an RREF witness.
-/
noncomputable def nullspaceMatrix (E : IsRREF M D) : Matrix R m (m - D.rank) := by
  sorry

/-- Temporary Phase 1 scaffold for nullspace basis vectors. -/
noncomputable def nullspace (E : IsRREF M D) : Vector (Vector R m) (m - D.rank) := by
  sorry

theorem nullspace_sound (E : IsRREF M D) (k : Fin (m - D.rank)) :
    M * E.nullspace[k] = 0 := by
  sorry

end IsRREF

theorem nullspace_complete {R : Type u} [Field R] {n m : Nat} {M : Matrix R n m}
    {D : RowEchelonData R n m} (E : IsRREF M D) (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - D.rank), E.nullspaceMatrix * c = v := by
  sorry

namespace Matrix

/-- Convenience wrapper: compute the scaffolded nullspace through RREF. -/
noncomputable def nullspace {R : Type u} [Field R] {n m : Nat} (M : Matrix R n m) :
    Vector (Vector R m) (m - (rref M).rank) := by
  sorry

end Matrix

end HexMatrix
