import Std
import Init.Grind.Ring.Field
import HexMatrix.RowEchelon

/-!
Determinant scaffolding for `hex-matrix`.

This module adds the generic Leibniz-formula determinant for dense square
matrices together with the determinant behavior of the elementary row
operations used by row reduction and Bareiss pivot tracking.
-/

namespace Hex

universe u

namespace Matrix

variable {α : Type u}

/-- Insert an element into a vector at a given position. -/
def insertAt (x : α) (v : Vector α n) (i : Fin (n + 1)) : Vector α (n + 1) :=
  ⟨(v.toList.insertIdx i.val x).toArray, by
    have hi : i.val ≤ v.toList.length := by
      simpa using Nat.lt_succ_iff.mp i.isLt
    simpa using List.length_insertIdx_of_le_length (a := x) (as := v.toList) hi⟩

/-- The unique empty vector. -/
def emptyVec : Vector α 0 :=
  ⟨#[], rfl⟩

/-- Enumerate the permutations of `Fin n` as length-`n` vectors. -/
def permutationVectors : (n : Nat) → List (Vector (Fin n) n)
  | 0 => [emptyVec]
  | n + 1 =>
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n)

/-- Count inversions in a permutation written as a list. -/
def inversionCount : List (Fin n) → Nat
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 + inversionCount xs

/-- The sign of a permutation vector, computed from inversion parity. -/
def detSign {R : Type u} [Lean.Grind.Ring R] {n : Nat} (perm : Vector (Fin n) n) : R :=
  if inversionCount perm.toList % 2 = 0 then 1 else -1

/-- The unsigned product associated to a permutation vector. -/
def detProduct {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  (List.finRange n).foldl (fun acc i => acc * M[i][perm[i]]) 1

/-- The Leibniz summand associated to a permutation vector. -/
def detTerm {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  detSign perm * detProduct M perm

/-- The determinant of a dense square matrix, defined by the Leibniz formula. -/
def det {R : Type u} [Lean.Grind.Ring R] {n : Nat} (M : Matrix R n n) : R :=
  (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0

theorem det_one {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    det (1 : Matrix R n n) = 1 := by
  sorry

theorem det_rowSwap {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i j : Fin n) (h : i ≠ j) :
    det (rowSwap M i j) = -det M := by
  sorry

theorem det_rowScale {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (i : Fin n) (c : R) :
    det (rowScale M i c) = c * det M := by
  sorry

theorem det_rowAdd {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) (c : R) (h : src ≠ dst) :
    det (rowAdd M src dst c) = det M := by
  sorry

end Matrix
end Hex
