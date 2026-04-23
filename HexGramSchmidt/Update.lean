import HexGramSchmidt.GramDet
import HexMatrix.RowOps

/-!
Row-operation update scaffolding for integer Gram-Schmidt data.

This module adds the Phase 1 update-formula surface used by downstream
LLL work: executable size-reduction and adjacent-swap row operations on
the integer basis, together with theorem statements describing how the
Gram-Schmidt basis, coefficient data, scaled coefficients, and Gram
determinants change under those operations.
-/

namespace Hex
namespace GramSchmidt
namespace Int

open HexMatrix

/--
Size-reduce row `k` against row `j` by replacing `b[k]` with
`b[k] - r * b[j]`.

Out-of-bounds indices leave the matrix unchanged so the theorem surface
can use the spec's Nat-indexed style.
-/
def sizeReduce (b : HexMatrix.Matrix Int n m) (k j : Nat) (r : Int) :
    HexMatrix.Matrix Int n m :=
  if hk : k < n then
    if hj : j < n then
      HexMatrix.Matrix.rowAdd b ⟨k, hk⟩ ⟨j, hj⟩ (-r)
    else
      b
  else
    b

/--
Swap adjacent rows `k - 1` and `k`.

Out-of-bounds indices leave the matrix unchanged so the executable
helper matches the Nat-indexed theorem statements below.
-/
def adjacentSwap (b : HexMatrix.Matrix Int n m) (k : Nat) :
    HexMatrix.Matrix Int n m :=
  if hk : k < n then
    if hkm1 : k - 1 < n then
      HexMatrix.Matrix.rowSwap b ⟨k, hk⟩ ⟨k - 1, hkm1⟩
    else
      b
  else
    b

/-- The new `(k - 1)`-st Gram-Schmidt basis row after swapping rows `k - 1` and `k`. -/
noncomputable def swappedBasisPrev (b : HexMatrix.Matrix Int n m) (k : Nat) :
    Vector Rat m :=
  HexMatrix.Matrix.row (basis (adjacentSwap b k)) (k - 1)

/-- The new `k`-th Gram-Schmidt basis row after swapping rows `k - 1` and `k`. -/
noncomputable def swappedBasisCurr (b : HexMatrix.Matrix Int n m) (k : Nat) :
    Vector Rat m :=
  HexMatrix.Matrix.row (basis (adjacentSwap b k)) k

theorem basis_sizeReduce (b : HexMatrix.Matrix Int n m)
    (k j : Nat) (_hk : k < n) (_hjk : j < k) (r : Int) :
    basis (sizeReduce b k j r) = basis b := by
  sorry

theorem coeffs_sizeReduce_pivot (b : HexMatrix.Matrix Int n m)
    (k j : Nat) (_hk : k < n) (hjk : j < k) (r : Int) :
    HexMatrix.Matrix.entry (coeffs (sizeReduce b k j r)) k j =
      HexMatrix.Matrix.entry (coeffs b) k j - r := by
  sorry

theorem coeffs_sizeReduce_lower (b : HexMatrix.Matrix Int n m)
    (k j l : Nat) (_hk : k < n) (hjk : j < k) (_hlj : l < j) (r : Int) :
    HexMatrix.Matrix.entry (coeffs (sizeReduce b k j r)) k l =
      HexMatrix.Matrix.entry (coeffs b) k l -
        r * HexMatrix.Matrix.entry (coeffs b) j l := by
  sorry

theorem gramDet_sizeReduce (b : HexMatrix.Matrix Int n m)
    (k j t : Nat) (_hk : k < n) (hjk : j < k) (r : Int) (ht : t ≤ n) :
    gramDet (sizeReduce b k j r) t ht = gramDet b t ht := by
  sorry

theorem scaledCoeffs_sizeReduce_pivot (b : HexMatrix.Matrix Int n m)
    (k j : Nat) (hk : k < n) (hjk : j < k) (r : Int) :
    HexMatrix.Matrix.entry (scaledCoeffs (sizeReduce b k j r)) k j =
      HexMatrix.Matrix.entry (scaledCoeffs b) k j -
        r * (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hjk hk)) : Int) := by
  sorry

theorem scaledCoeffs_sizeReduce_lower (b : HexMatrix.Matrix Int n m)
    (k j l : Nat) (_hk : k < n) (hjk : j < k) (_hlj : l < j) (r : Int) :
    HexMatrix.Matrix.entry (scaledCoeffs (sizeReduce b k j r)) k l =
      HexMatrix.Matrix.entry (scaledCoeffs b) k l -
        r * HexMatrix.Matrix.entry (scaledCoeffs b) j l := by
  sorry

theorem basis_adjacentSwap_other (b : HexMatrix.Matrix Int n m)
    (k i : Nat) (_hk : k < n) (_hpos : 0 < k) (_hi : i < n)
    (hiPrev : i ≠ k - 1) (hiCurr : i ≠ k) :
    HexMatrix.Matrix.row (basis (adjacentSwap b k)) i =
      HexMatrix.Matrix.row (basis b) i := by
  sorry

theorem basis_adjacentSwap_prev (b : HexMatrix.Matrix Int n m)
    (k : Nat) (_hk : k < n) (_hpos : 0 < k) :
    HexMatrix.Matrix.row (basis (adjacentSwap b k)) (k - 1) =
      HexMatrix.Matrix.row (basis b) k +
        HexMatrix.Matrix.entry (coeffs b) k (k - 1) •
          HexMatrix.Matrix.row (basis b) (k - 1) := by
  sorry

theorem basis_adjacentSwap_curr (b : HexMatrix.Matrix Int n m)
    (k : Nat) (hk : k < n) (_hpos : 0 < k) (hkm1 : k - 1 ≤ n) :
    HexMatrix.Matrix.row (basis (adjacentSwap b k)) k =
      ((((gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Nat) : Rat) *
            ((gramDet b (k - 1) hkm1 : Nat) : Rat)) /
          (((gramDet b k (Nat.le_of_lt hk) : Nat) : Rat) *
            (gramDet (adjacentSwap b k) k (Nat.le_of_lt hk) : Rat))) •
          HexMatrix.Matrix.row (basis b) (k - 1) -
        ((((HexMatrix.Matrix.entry (scaledCoeffs b) k (k - 1) : Int) : Rat) /
            (gramDet (adjacentSwap b k) k (Nat.le_of_lt hk) : Rat))) •
          HexMatrix.Matrix.row (basis b) k := by
  sorry

theorem gramDet_adjacentSwap_other (b : HexMatrix.Matrix Int n m)
    (k t : Nat) (_hk : k < n) (_hpos : 0 < k) (ht : t ≤ n) (htk : t ≠ k) :
    gramDet (adjacentSwap b k) t ht = gramDet b t ht := by
  sorry

theorem gramDet_adjacentSwap_pivot (b : HexMatrix.Matrix Int n m)
    (k : Nat) (hk : k < n) (_hpos : 0 < k) (hkm1 : k - 1 ≤ n) :
    (gramDet (adjacentSwap b k) k (Nat.le_of_lt hk) : Rat) =
      (((gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Nat) : Rat) *
          ((gramDet b (k - 1) hkm1 : Nat) : Rat) +
        ((HexMatrix.Matrix.entry (scaledCoeffs b) k (k - 1) : Int) : Rat) ^ (2 : Nat)) /
        ((gramDet b k (Nat.le_of_lt hk) : Nat) : Rat) := by
  sorry

theorem scaledCoeffs_adjacentSwap_pivot (b : HexMatrix.Matrix Int n m)
    (k : Nat) (_hk : k < n) (_hpos : 0 < k) :
    HexMatrix.Matrix.entry (scaledCoeffs (adjacentSwap b k)) k (k - 1) =
      HexMatrix.Matrix.entry (scaledCoeffs b) k (k - 1) := by
  sorry

theorem scaledCoeffs_adjacentSwap_prev (b : HexMatrix.Matrix Int n m)
    (k j : Nat) (_hk : k < n) (_hpos : 0 < k) (_hj : j < k - 1) :
    HexMatrix.Matrix.entry (scaledCoeffs (adjacentSwap b k)) (k - 1) j =
      HexMatrix.Matrix.entry (scaledCoeffs b) k j := by
  sorry

theorem scaledCoeffs_adjacentSwap_curr (b : HexMatrix.Matrix Int n m)
    (k j : Nat) (_hk : k < n) (_hpos : 0 < k) (_hj : j < k - 1) :
    HexMatrix.Matrix.entry (scaledCoeffs (adjacentSwap b k)) k j =
      HexMatrix.Matrix.entry (scaledCoeffs b) (k - 1) j := by
  sorry

theorem coeffs_adjacentSwap_other (b : HexMatrix.Matrix Int n m)
    (k i j : Nat) (_hk : k < n) (_hpos : 0 < k) (_hi : i < n) (_hj : j < n)
    (hiPrev : i ≠ k - 1) (hiCurr : i ≠ k)
    (hjPrev : j ≠ k - 1) (hjCurr : j ≠ k) :
    HexMatrix.Matrix.entry (coeffs (adjacentSwap b k)) i j =
      HexMatrix.Matrix.entry (coeffs b) i j := by
  sorry

theorem coeffs_adjacentSwap_pivot (b : HexMatrix.Matrix Int n m)
    (k : Nat) (hk : k < n) (_hpos : 0 < k) :
    HexMatrix.Matrix.entry (coeffs (adjacentSwap b k)) k (k - 1) =
      (((HexMatrix.Matrix.entry (scaledCoeffs b) k (k - 1) : Int) : Rat) /
        (gramDet (adjacentSwap b k) k (Nat.le_of_lt hk) : Rat)) := by
  sorry

theorem coeffs_adjacentSwap_prev (b : HexMatrix.Matrix Int n m)
    (k j : Nat) (_hk : k < n) (_hpos : 0 < k) (_hj : j < k - 1) :
    HexMatrix.Matrix.entry (coeffs (adjacentSwap b k)) (k - 1) j =
      HexMatrix.Matrix.entry (coeffs b) k j := by
  sorry

theorem coeffs_adjacentSwap_curr (b : HexMatrix.Matrix Int n m)
    (k j : Nat) (_hk : k < n) (_hpos : 0 < k) (_hj : j < k - 1) :
    HexMatrix.Matrix.entry (coeffs (adjacentSwap b k)) k j =
      HexMatrix.Matrix.entry (coeffs b) (k - 1) j := by
  sorry

theorem scaledCoeffs_adjacentSwap_tail_prev (b : HexMatrix.Matrix Int n m)
    (k i : Nat) (hk : k < n) (hpos : 0 < k) (_hik : k < i) (_hi : i < n) :
    ((HexMatrix.Matrix.entry (scaledCoeffs (adjacentSwap b k)) i (k - 1) : Int) : Rat) =
      ((((HexMatrix.Matrix.entry (scaledCoeffs b) i (k - 1) : Int) : Rat) *
          (gramDet (adjacentSwap b k) k (Nat.le_of_lt hk) : Rat)) +
        (((HexMatrix.Matrix.entry (scaledCoeffs b) i k : Int) : Rat) *
          ((HexMatrix.Matrix.entry (scaledCoeffs b) k (k - 1) : Int) : Rat))) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  sorry

theorem scaledCoeffs_adjacentSwap_tail_curr (b : HexMatrix.Matrix Int n m)
    (k i : Nat) (hk : k < n) (hpos : 0 < k) (hkm1 : k - 1 ≤ n) (_hik : k < i) (_hi : i < n) :
    ((HexMatrix.Matrix.entry (scaledCoeffs (adjacentSwap b k)) i k : Int) : Rat) =
      ((((HexMatrix.Matrix.entry (scaledCoeffs b) i k : Int) : Rat) *
          ((gramDet b (k - 1) hkm1 : Nat) : Rat)) -
        (((HexMatrix.Matrix.entry (scaledCoeffs b) i (k - 1) : Int) : Rat) *
          ((HexMatrix.Matrix.entry (scaledCoeffs b) k (k - 1) : Int) : Rat))) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  sorry

theorem coeffs_adjacentSwap_tail_prev (b : HexMatrix.Matrix Int n m)
    (k i : Nat) (hk : k < n) (_hpos : 0 < k) (_hik : k < i) (_hi : i < n) :
    HexMatrix.Matrix.entry (coeffs (adjacentSwap b k)) i (k - 1) =
      (((((HexMatrix.Matrix.entry (scaledCoeffs b) i (k - 1) : Int) : Rat) *
            (gramDet (adjacentSwap b k) k (Nat.le_of_lt hk) : Rat)) +
          (((HexMatrix.Matrix.entry (scaledCoeffs b) i k : Int) : Rat) *
            ((HexMatrix.Matrix.entry (scaledCoeffs b) k (k - 1) : Int) : Rat))) /
        (gramDet b k (Nat.le_of_lt hk) : Rat)) /
        (gramDet (adjacentSwap b k) k (Nat.le_of_lt hk) : Rat) := by
  sorry

theorem coeffs_adjacentSwap_tail_curr (b : HexMatrix.Matrix Int n m)
    (k i : Nat) (hk : k < n) (_hpos : 0 < k) (hkm1 : k - 1 ≤ n)
    (_hik : k < i) (_hi : i < n) :
    HexMatrix.Matrix.entry (coeffs (adjacentSwap b k)) i k =
      (((((HexMatrix.Matrix.entry (scaledCoeffs b) i k : Int) : Rat) *
            ((gramDet b (k - 1) hkm1 : Nat) : Rat)) -
          (((HexMatrix.Matrix.entry (scaledCoeffs b) i (k - 1) : Int) : Rat) *
            ((HexMatrix.Matrix.entry (scaledCoeffs b) k (k - 1) : Int) : Rat))) /
        (gramDet b k (Nat.le_of_lt hk) : Rat)) /
        (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) := by
  sorry

end Int
end GramSchmidt
end Hex
