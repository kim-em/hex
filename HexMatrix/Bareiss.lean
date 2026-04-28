import HexMatrix.Determinant

/-!
Executable Bareiss determinant algorithm for `hex-matrix`.

This module implements fraction-free Bareiss elimination over `Int` in two
layers: a no-pivot recurrence that follows the standard exact-division update,
and a public row-pivoting wrapper that swaps in a nonzero pivot when needed and
tracks the resulting determinant sign. The root library also exposes the
theorem surface relating this executable path to the generic determinant.
-/

namespace Hex

universe u

namespace Matrix

variable {n : Nat}

/-- Output of an executable Bareiss elimination pass. -/
structure BareissData (n : Nat) where
  matrix : Matrix Int n n
  rowSwaps : Nat
  singularStep : Option Nat

namespace BareissData

/-- The determinant sign contributed by the recorded row swaps. -/
def sign (data : BareissData n) : Int :=
  if data.rowSwaps % 2 = 0 then 1 else -1

private def lastDiag? (M : Matrix Int n n) : Option Int :=
  match n with
  | 0 => none
  | k + 1 =>
      let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      some M[i][i]

/-- The determinant encoded by a Bareiss elimination result. -/
def det (data : BareissData n) : Int :=
  match data.singularStep with
  | some _ => 0
  | none =>
      match lastDiag? data.matrix with
      | some d => data.sign * d
      | none => data.sign

end BareissData

private structure BareissState (n : Nat) where
  step : Nat
  matrix : Matrix Int n n
  prevPivot : Int
  rowSwaps : Nat
  singularStep : Option Nat

/-- Exact division used by the Bareiss recurrence. The `else` branch is
defensive; for matrices produced by the Bareiss update, divisibility should
always hold. -/
private def exactDiv (num denom : Int) : Int :=
  if h : denom ∣ num then
    Int.divExact num denom h
  else
    0

/-- Search column `col` for a nonzero pivot at or below `start`. -/
private def findPivotAux (M : Matrix Int n n) (col : Fin n) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[i][col] = 0 then
          findPivotAux M col (start + 1) fuel
        else
          some i
      else
        none

/-- Search column `col` for a nonzero pivot at or below `start`. -/
private def findPivot? (M : Matrix Int n n) (col : Fin n) (start : Nat) :
    Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- Apply one Bareiss update step to the trailing submatrix strictly below and
to the right of the current pivot. -/
private def stepMatrix (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) :
    Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if hkij : k < i.val ∧ k < j.val then
      let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
      let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
      exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot
    else if hBelow : k < i.val ∧ j.val = k then
      0
    else
      M[i][j]

private def finish (state : BareissState n) : BareissData n :=
  { matrix := state.matrix
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- Bareiss elimination without pivoting. A zero pivot aborts and records the
singular step. -/
private def noPivotLoop (fuel : Nat) (state : BareissState n) : BareissState n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let pivot := state.matrix[k][k]
        if hp : pivot = 0 then
          { state with singularStep := some state.step }
        else
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix state.matrix state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := state.rowSwaps
              singularStep := none }
          noPivotLoop fuel next
      else
        state

/-- Bareiss elimination with row pivoting. If a column has no nonzero pivot,
the elimination aborts and the determinant is zero. -/
private def pivotLoop (fuel : Nat) (state : BareissState n) : BareissState n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let (M, swaps) :=
          if state.matrix[k][k] = 0 then
            match findPivot? state.matrix k (state.step + 1) with
            | some pivot => (rowSwap state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := M[k][k]
        if hp : pivot = 0 then
          { state with matrix := M, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix M state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotLoop fuel next
      else
        state

/-- Run the no-pivot Bareiss recurrence and return the final elimination data. -/
def bareissNoPivotData (M : Matrix Int n n) : BareissData n :=
  finish <| noPivotLoop n
    { step := 0
      matrix := M
      prevPivot := 1
      rowSwaps := 0
      singularStep := none }

/-- Determinant computed by the no-pivot Bareiss recurrence. -/
def bareissNoPivot (M : Matrix Int n n) : Int :=
  (bareissNoPivotData M).det

/-- Run the row-pivoted Bareiss elimination and return the final elimination
data together with the swap/sign bookkeeping. -/
def bareissData (M : Matrix Int n n) : BareissData n :=
  finish <| pivotLoop n
    { step := 0
      matrix := M
      prevPivot := 1
      rowSwaps := 0
      singularStep := none }

/-- Determinant computed by the row-pivoted Bareiss algorithm. -/
def bareiss (M : Matrix Int n n) : Int :=
  (bareissData M).det

/-- The Bareiss determinant agrees with the generic determinant. -/
theorem bareiss_eq_det (M : Matrix Int n n) :
    bareiss M = det M := by
  sorry

end Matrix
end Hex
