import HexLLL.SizeReduce

/-!
Executable adjacent-swap scaffolding for the LLL integer state.

This module adds the second algorithmic state transition required by the
`HexLLL` Phase 1 scaffold: swapping rows `k - 1` and `k` in the current
basis and rebuilding the cached integer Gram-Schmidt state. The
executable definition follows the existing `ofBasis` style, while the
auxiliary exact-division helpers and theorem surface record the
specification's integer update formulas for later proof work.
-/

namespace HexLLL

open HexMatrix

namespace LLLState

/-- Exact Nat division helper for swap-step Gram-determinant updates. -/
def exactDivNat (num den : Nat) : Nat :=
  num / den

/--
Exact Int division helper for swap-step scaled-coefficient updates.

The helper returns `0` when the denominator vanishes so the surrounding
Nat-indexed API remains total at out-of-bounds indices.
-/
def exactDivInt (num den : Int) : Int :=
  if den = 0 then
    0
  else
    Int.fdiv num den

/-- Adjacent basis swap underlying the LLL swap transition. -/
def swapBasis (s : LLLState n m) (k : Nat) : HexMatrix.Matrix Int n m :=
  Hex.GramSchmidt.Int.adjacentSwap s.b k

/-- The stored scaled pivot coefficient `ν[k, k - 1]` used by the swap formulas. -/
def swapPivotCoeff (s : LLLState n m) (k : Nat) : Int :=
  HexMatrix.Matrix.entry s.ν k (k - 1)

/-- The spec's numerator for the updated pivot Gram determinant `d[k]`. -/
def swapGramDetNumerator (s : LLLState n m) (k : Nat) : Nat :=
  s.gramDetEntry (k + 1) * s.gramDetEntry (k - 1) + Int.natAbs (swapPivotCoeff s k) ^ 2

/-- The exact-division update for the swapped pivot Gram determinant. -/
def swapGramDetValue (s : LLLState n m) (k : Nat) : Nat :=
  exactDivNat (swapGramDetNumerator s k) (s.gramDetEntry k)

/-- Numerator for the updated `ν[i, k - 1]` entry after the swap. -/
def swapTailPrevNumerator (s : LLLState n m) (i k : Nat) : Int :=
  HexMatrix.Matrix.entry s.ν i (k - 1) * (swapGramDetValue s k : Int) +
    HexMatrix.Matrix.entry s.ν i k * swapPivotCoeff s k

/-- Numerator for the updated `ν[i, k]` entry after the swap. -/
def swapTailCurrNumerator (s : LLLState n m) (i k : Nat) : Int :=
  HexMatrix.Matrix.entry s.ν i k * (s.gramDetEntry (k - 1) : Int) -
    HexMatrix.Matrix.entry s.ν i (k - 1) * swapPivotCoeff s k

/-- Exact-division value for the updated `ν[i, k - 1]` entry after the swap. -/
def swapTailPrevValue (s : LLLState n m) (i k : Nat) : Int :=
  exactDivInt (swapTailPrevNumerator s i k) (s.gramDetEntry k : Int)

/-- Exact-division value for the updated `ν[i, k]` entry after the swap. -/
def swapTailCurrValue (s : LLLState n m) (i k : Nat) : Int :=
  exactDivInt (swapTailCurrNumerator s i k) (s.gramDetEntry k : Int)

/--
Swap rows `k - 1` and `k`, then rebuild the cached integer
Gram-Schmidt state from the updated basis.
-/
def swapStep (s : LLLState n m) (k : Nat) : LLLState n m :=
  ofBasis (swapBasis s k)

theorem swapStep_basis_eq (s : LLLState n m) (k : Nat) :
    (swapStep s k).b = swapBasis s k := by
  rfl

theorem swapStep_pivotCoeff (s : LLLState n m) (k : Nat)
    (hk : k < n) (hpos : 0 < k) :
    HexMatrix.Matrix.entry (swapStep s k).ν k (k - 1) = swapPivotCoeff s k := by
  sorry

theorem swapStep_gramDet_pivot (s : LLLState n m) (k : Nat)
    (hk : k < n) (hpos : 0 < k) :
    (swapStep s k).gramDetEntry k = swapGramDetValue s k := by
  sorry

theorem swapStep_prev_row_entry (s : LLLState n m) (k j : Nat)
    (hk : k < n) (hpos : 0 < k) (hj : j < k - 1) :
    HexMatrix.Matrix.entry (swapStep s k).ν (k - 1) j =
      HexMatrix.Matrix.entry s.ν k j := by
  sorry

theorem swapStep_curr_row_entry (s : LLLState n m) (k j : Nat)
    (hk : k < n) (hpos : 0 < k) (hj : j < k - 1) :
    HexMatrix.Matrix.entry (swapStep s k).ν k j =
      HexMatrix.Matrix.entry s.ν (k - 1) j := by
  sorry

theorem swapStep_tail_prev_entry (s : LLLState n m) (i k : Nat)
    (hk : k < n) (hpos : 0 < k) (hik : k < i) (hi : i < n) :
    HexMatrix.Matrix.entry (swapStep s k).ν i (k - 1) = swapTailPrevValue s i k := by
  sorry

theorem swapStep_tail_curr_entry (s : LLLState n m) (i k : Nat)
    (hk : k < n) (hpos : 0 < k) (hik : k < i) (hi : i < n) :
    HexMatrix.Matrix.entry (swapStep s k).ν i k = swapTailCurrValue s i k := by
  sorry

end LLLState
end HexLLL
