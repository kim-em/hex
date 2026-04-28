import HexMatrix.Basic

/-!
Row operations and echelon-form data for `hex-matrix`.

This module adds executable row-operation helpers together with the pure data
structures and contracts used by later row-reduction, span/nullspace, and
determinant routines.
-/

namespace Hex

universe u

namespace Matrix

/-- Swap rows `i` and `j` in a dense matrix. -/
def rowSwap (M : Matrix R n m) (i j : Fin n) : Matrix R n m :=
  (M.set i M[j]).set j M[i]

/-- Scale row `i` by `c`. -/
def rowScale [Mul R] (M : Matrix R n m) (i : Fin n) (c : R) : Matrix R n m :=
  M.set i <| Vector.ofFn fun k => c * M[i][k]

/-- Replace row `dst` by `row dst + c * row src`. -/
def rowAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin n) (c : R) : Matrix R n m :=
  M.set dst <| Vector.ofFn fun k => M[dst][k] + c * M[src][k]

/-- Pure data produced by an echelon-form algorithm. -/
structure RowEchelonData (R : Type u) (n m : Nat) where
  rank : Nat
  echelon : Matrix R n m
  transform : Matrix R n n
  pivotCols : Vector (Fin m) rank

/-- Shared conditions for any echelon form. -/
structure IsEchelonForm [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (M : Matrix R n m) (D : RowEchelonData R n m) : Prop where
  transform_mul : D.transform * M = D.echelon
  transform_inv : ∃ Tinv : Matrix R n n, Tinv * D.transform = 1
  rank_le_n : D.rank ≤ n
  rank_le_m : D.rank ≤ m
  pivotCols_sorted : ∀ i j, i < j → D.pivotCols.get i < D.pivotCols.get j
  below_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      i.val < j.val → D.echelon[j][D.pivotCols.get i] = 0
  zero_row : ∀ (i : Fin n), D.rank ≤ i.val → D.echelon[i] = 0

/-- RREF-specific conditions on top of `IsEchelonForm`. -/
structure IsRREF [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (M : Matrix R n m) (D : RowEchelonData R n m)
    : Prop extends IsEchelonForm M D where
  pivot_one : ∀ (i : Fin D.rank), D.echelon[i][D.pivotCols.get i] = 1
  above_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      j.val < i.val → D.echelon[j][D.pivotCols.get i] = 0

namespace IsEchelonForm

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}

/-- A left inverse for the square row-transform yields a right inverse. -/
theorem transform_mul_inv (E : IsEchelonForm M D) :
    ∃ Tinv : Matrix R n n, D.transform * Tinv = 1 := by
  sorry

/-- The pivot columns are injective because they are strictly increasing. -/
theorem pivotCols_injective (E : IsEchelonForm M D) :
    Function.Injective fun i : Fin D.rank => D.pivotCols.get i := by
  sorry

/-- The non-pivot columns, enumerated in increasing order. -/
def freeColsList (_E : IsEchelonForm M D) : List (Fin m) :=
  (List.finRange m).filter fun j => j ∉ D.pivotCols.toList

theorem freeColsList_length (E : IsEchelonForm M D) :
    E.freeColsList.length = m - D.rank := by
  sorry

/-- Sorted complement of the pivot columns. -/
def freeCols (E : IsEchelonForm M D) : Vector (Fin m) (m - D.rank) :=
  ⟨E.freeColsList.toArray, by simpa using E.freeColsList_length⟩

theorem freeCols_sorted (E : IsEchelonForm M D) :
    ∀ i j, i < j → E.freeCols.get i < E.freeCols.get j := by
  sorry

/-- The free columns are injective because they are strictly increasing. -/
theorem freeCols_injective (E : IsEchelonForm M D) :
    Function.Injective fun i : Fin (m - D.rank) => E.freeCols.get i := by
  sorry

/-- Every column is either a pivot column or a free column. -/
theorem colPartition (E : IsEchelonForm M D) (j : Fin m) :
    (∃ i : Fin D.rank, D.pivotCols.get i = j) ∨
    (∃ k : Fin (m - D.rank), E.freeCols.get k = j) := by
  sorry

theorem colPartition_exclusive (E : IsEchelonForm M D) (j : Fin m) :
    ¬((∃ i : Fin D.rank, D.pivotCols.get i = j) ∧
      (∃ k : Fin (m - D.rank), E.freeCols.get k = j)) := by
  sorry

/-- No column can be both pivot and free. -/
theorem pivotCols_disjoint_freeCols (E : IsEchelonForm M D) :
    ∀ (i : Fin D.rank) (k : Fin (m - D.rank)),
      D.pivotCols.get i ≠ E.freeCols.get k := by
  sorry

end IsEchelonForm

end Matrix
end Hex
