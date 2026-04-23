import HexMatrix.RowOps

/-!
RREF and column-partition scaffolding for dense matrices.

This module introduces the Phase 1 API surface for reduced row-echelon
reduction together with the free-column partition interface used by later
span and nullspace development.
-/
namespace HexMatrix

universe u

open Lean.Grind

namespace RrefImpl

variable {R : Type u} [Field R] [DecidableEq R]

private structure State (n m : Nat) where
  echelon : Matrix R n m
  transform : Matrix R n n
  rank : Nat
  pivotCols : Array (Fin m)
  pivotCols_size : pivotCols.size = rank

private def init (M : Matrix R n m) : State (R := R) n m where
  echelon := M
  transform := 1
  rank := 0
  pivotCols := #[]
  pivotCols_size := rfl

private def findPivotRow? (M : Matrix R n m) (start : Nat) (col : Fin m) : Option (Fin n) :=
  let rec loop (i remaining : Nat) : Option (Fin n) :=
    match remaining with
    | 0 => none
    | remaining + 1 =>
        if h : i < n then
          let row : Fin n := ⟨i, h⟩
          if M[row][col] = 0 then
            loop (i + 1) remaining
          else
            some row
        else
          none
  loop start (n - start)

private def clearPivotColumn
    (echelon : Matrix R n m) (transform : Matrix R n n) (pivotRow : Fin n) (col : Fin m) :
    Matrix R n m × Matrix R n n :=
  let rec loop (i remaining : Nat) (A : Matrix R n m) (T : Matrix R n n) :
      Matrix R n m × Matrix R n n :=
    match remaining with
    | 0 => (A, T)
    | remaining + 1 =>
        if h : i < n then
          let row : Fin n := ⟨i, h⟩
          if hRow : row = pivotRow then
            loop (i + 1) remaining A T
          else
            let coeff := -A[row][col]
            let A' := if coeff = 0 then A else Matrix.rowAdd A row pivotRow coeff
            let T' := if coeff = 0 then T else Matrix.rowAdd T row pivotRow coeff
            loop (i + 1) remaining A' T'
        else
          (A, T)
  loop 0 n echelon transform

private def eliminateAt
    (S : State (R := R) n m) (row pivotRow : Fin n) (col : Fin m) :
    State (R := R) n m :=
  let swappedEchelon := Matrix.rowSwap S.echelon row pivotRow
  let swappedTransform := Matrix.rowSwap S.transform row pivotRow
  let pivotInv := (swappedEchelon[row][col])⁻¹
  let scaledEchelon := Matrix.rowScale swappedEchelon row pivotInv
  let scaledTransform := Matrix.rowScale swappedTransform row pivotInv
  let (reducedEchelon, reducedTransform) :=
    clearPivotColumn (R := R) scaledEchelon scaledTransform row col
  { echelon := reducedEchelon
    transform := reducedTransform
    rank := S.rank + 1
    pivotCols := S.pivotCols.push col
    pivotCols_size := by
      simp [Array.size_push, S.pivotCols_size] }

private def runColumns (remaining col : Nat) (S : State (R := R) n m) :
    State (R := R) n m :=
  match remaining with
  | 0 => S
  | remaining + 1 =>
      if hCol : col < m then
        if hRow : S.rank < n then
          let pivotCol : Fin m := ⟨col, hCol⟩
          match findPivotRow? (R := R) S.echelon S.rank pivotCol with
          | none =>
              runColumns remaining (col + 1) S
          | some pivotRow =>
              let row : Fin n := ⟨S.rank, hRow⟩
              let S' := eliminateAt (R := R) S row pivotRow pivotCol
              runColumns remaining (col + 1) S'
        else
          S
      else
        S

private def run (M : Matrix R n m) : State (R := R) n m :=
  runColumns (R := R) m 0 (init (R := R) M)

private def toRowEchelonData (S : State (R := R) n m) : RowEchelonData R n m where
  rank := S.rank
  echelon := S.echelon
  transform := S.transform
  pivotCols := ⟨S.pivotCols, S.pivotCols_size⟩

end RrefImpl

/-- Executable dense reduced row-echelon reduction over decidable fields. -/
def rref {R : Type u} [Field R] [DecidableEq R] (M : Matrix R n m) : RowEchelonData R n m :=
  RrefImpl.toRowEchelonData (R := R) (RrefImpl.run (R := R) M)

/-- The scaffolded `rref` output satisfies the intended RREF interface. -/
theorem rref_isRREF {R : Type u} [Field R] [DecidableEq R] (M : Matrix R n m) :
    IsRREF M (rref M) := by
  sorry

namespace IsEchelonForm

variable {R : Type u} [Zero R] [One R] [Add R] [Mul R]
variable {n m : Nat} {M : Matrix R n m} {D : RowEchelonData R n m}

/--
Temporary Phase 1 scaffold upgrading the recorded left inverse of the
transform matrix to a right inverse for the square `n × n` case.
-/
theorem transform_mul_inv (E : IsEchelonForm M D) :
    ∃ Tinv : Matrix R n n, D.transform * Tinv = 1 := by
  sorry

/--
Temporary Phase 1 scaffold for the sorted complement of the pivot columns.
-/
noncomputable def freeCols (E : IsEchelonForm M D) : Vector (Fin m) (m - D.rank) := by
  sorry

theorem freeCols_sorted (E : IsEchelonForm M D) :
    ∀ (i j : Fin (m - D.rank)), i.val < j.val → E.freeCols[i] < E.freeCols[j] := by
  sorry

/-- The sorted pivot-column vector has no duplicates. -/
theorem pivotCols_injective (E : IsEchelonForm M D) :
    Function.Injective (fun i : Fin D.rank => D.pivotCols[i]) := by
  sorry

/-- The sorted free-column vector has no duplicates. -/
theorem freeCols_injective (E : IsEchelonForm M D) :
    Function.Injective (fun k : Fin (m - D.rank) => E.freeCols[k]) := by
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

/-- No pivot column appears in the free-column complement. -/
theorem pivotCols_disjoint_freeCols (E : IsEchelonForm M D)
    (i : Fin D.rank) (k : Fin (m - D.rank)) :
    D.pivotCols[i] ≠ E.freeCols[k] := by
  sorry

end IsEchelonForm

end HexMatrix
