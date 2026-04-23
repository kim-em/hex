import HexMatrix.RowEchelon

/-!
RREF and column-partition scaffolding for dense matrices.

This module introduces the Phase 1 API surface for reduced row-echelon
reduction together with the free-column partition interface used by later
span and nullspace development.
-/
namespace HexMatrix

universe u

open Lean.Grind

/-- Temporary Phase 1 scaffold for dense reduced row-echelon reduction. -/
def rref {R : Type u} [Field R] (M : Matrix R n m) : RowEchelonData R n m where
  rank := 0
  echelon := M
  transform := 1
  pivotCols := Vector.ofFn (fun i => nomatch i)

/-- The scaffolded `rref` output satisfies the intended RREF interface. -/
theorem rref_isRREF {R : Type u} [Field R] (M : Matrix R n m) : IsRREF M (rref M) := by
  sorry

namespace IsEchelonForm

variable {R : Type u} [Zero R] [One R] [Add R] [Mul R]
variable {n m : Nat} {M : Matrix R n m} {D : RowEchelonData R n m}

/--
Temporary Phase 1 scaffold for the sorted complement of the pivot columns.
-/
def freeCols (E : IsEchelonForm M D) : Vector (Fin m) (m - D.rank) :=
  let _hRank : D.rank ≤ m := E.rank_le_m
  Vector.ofFn (fun k =>
    ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.sub_le _ _)⟩)

theorem freeCols_sorted (E : IsEchelonForm M D) :
    ∀ (i j : Fin (m - D.rank)), i.val < j.val → E.freeCols[i] < E.freeCols[j] := by
  sorry

/-- Every column is either a pivot column or a free column. -/
theorem colPartition (E : IsEchelonForm M D) (j : Fin m) :
    (∃ i : Fin D.rank, D.pivotCols[i] = j) ∨
    (∃ k : Fin (m - D.rank), E.freeCols[k] = j) := by
  sorry

/-- No column is simultaneously pivot and free. -/
theorem colPartition_exclusive (E : IsEchelonForm M D) (j : Fin m) :
    ¬((∃ i : Fin D.rank, D.pivotCols[i] = j) ∧
      (∃ k : Fin (m - D.rank), E.freeCols[k] = j)) := by
  sorry

end IsEchelonForm

end HexMatrix
