import HexMatrix.RowEchelon

/-!
Determinant scaffolding for dense matrices.

This module adds an executable Phase 1 determinant definition for the
dense `HexMatrix.Matrix` representation using the Leibniz formula,
together with the adjacent public theorem surface expected by later
matrix work.
-/
namespace HexMatrix

universe u

open Lean.Grind

namespace Determinant

variable {α : Type u}

/-- Insert `x` after the first `k` elements of `xs`, or at the end if `k` is too large. -/
def insertAt (k : Nat) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
      match k with
      | 0 => x :: y :: ys
      | k' + 1 => y :: insertAt k' x ys

/-- All ways to insert `x` into `xs`. -/
def allInsertions (x : α) (xs : List α) : List (List α) :=
  (List.range (xs.length + 1)).map fun k => insertAt k x xs

/-- A simple executable permutation generator for lists. -/
def permutations : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
      ((permutations xs).map (allInsertions x)).foldr (· ++ ·) []

/-- Count inversions in a list of naturals. -/
def inversionCount : List Nat → Nat
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 + inversionCount xs

end Determinant

namespace Matrix

variable {R : Type u} {n : Nat}

/-- The sign attached to a permutation in the Leibniz formula. -/
def permSign [One R] [Neg R] (σ : List (Fin n)) : R :=
  if Determinant.inversionCount (σ.map Fin.val) % 2 = 0 then 1 else -1

/--
The Leibniz summand associated to a permutation, multiplying one entry
from each column in order.
-/
def permTermAux [One R] [Mul R] (M : Matrix R n n) : Nat → List (Fin n) → R
  | _, [] => 1
  | j, i :: is =>
      if h : j < n then
        let col : Fin n := ⟨j, h⟩
        M[i][col] * permTermAux M (j + 1) is
      else
        1

/--
The Leibniz summand associated to a permutation, multiplying one entry
from each column in order.
-/
def permTerm [One R] [Mul R] (M : Matrix R n n) (σ : List (Fin n)) : R :=
  permTermAux M 0 σ

/--
Executable determinant scaffold using the Leibniz formula over the
permutations of `Fin n`.
-/
def det [Zero R] [One R] [Add R] [Mul R] [Neg R] (M : Matrix R n n) : R :=
  (Determinant.permutations (List.finRange n)).foldl
    (fun acc σ => acc + permSign σ * permTerm M σ)
    0

end Matrix

open Matrix

/-- The determinant of the identity matrix is `1`. -/
theorem det_one {R : Type u} [CommRing R] {n : Nat} :
    Matrix.det ((Matrix.identity : Matrix R n n)) = 1 := by
  sorry

end HexMatrix
