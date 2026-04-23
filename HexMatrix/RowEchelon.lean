import Std

/-!
Row-echelon scaffolding for dense matrices.

This module introduces the dense `Matrix` alias together with the
row-echelon data and predicate layer used by later reduction algorithms.
-/
namespace HexMatrix

universe u

/-- Dense matrices are vectors of row vectors. -/
abbrev Matrix (R : Type u) (n m : Nat) := Vector (Vector R m) n

namespace Matrix

variable {R : Type u}

/-- Vectors inherit a pointwise zero from their entries. -/
instance instZeroVector [Zero R] : Zero (Vector R n) where
  zero := Vector.replicate n 0

/-- Dot product of two vectors. -/
def dot [Zero R] [Add R] [Mul R] (u v : Vector R n) : R :=
  (List.finRange n).foldl (fun acc i => acc + u[i] * v[i]) 0

/-- Extract a column from a dense matrix. -/
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Vector.ofFn (fun i => M[i][j])

/-- Identity matrix on `n` coordinates. -/
def identity [Zero R] [One R] : Matrix R n n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => if i = j then 1 else 0))

instance instHMul [Zero R] [Add R] [Mul R] :
    HMul (Matrix R n k) (Matrix R k m) (Matrix R n m) where
  hMul A B :=
    Vector.ofFn (fun i => Vector.ofFn (fun j => dot A[i] (col B j)))

instance instOne [Zero R] [One R] : One (Matrix R n n) where
  one := identity

end Matrix

/-- Pure data extracted from row reduction. -/
structure RowEchelonData (R : Type u) (n m : Nat) where
  rank : Nat
  echelon : Matrix R n m
  transform : Matrix R n n
  pivotCols : Vector (Fin m) rank

/-- Shared conditions for any echelon form. -/
structure IsEchelonForm
    {R : Type u} [Zero R] [One R] [Add R] [Mul R]
    {n m : Nat} (M : Matrix R n m) (D : RowEchelonData R n m) : Prop where
  transform_mul : D.transform * M = D.echelon
  transform_inv : ∃ Tinv : Matrix R n n, Tinv * D.transform = 1
  rank_le_n : D.rank ≤ n
  rank_le_m : D.rank ≤ m
  pivotCols_sorted : ∀ (i j : Fin D.rank), i.val < j.val → D.pivotCols[i] < D.pivotCols[j]
  below_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      i.val < j.val → D.echelon[j][D.pivotCols[i]] = 0
  zero_row : ∀ (i : Fin n), D.rank ≤ i.val → D.echelon[i] = 0

/-- RREF-specific conditions on top of a generic echelon form. -/
structure IsRREF
    {R : Type u} [Zero R] [One R] [Add R] [Mul R]
    {n m : Nat} (M : Matrix R n m) (D : RowEchelonData R n m)
    : Prop extends IsEchelonForm M D where
  pivot_one : ∀ (i : Fin D.rank), D.echelon[i][D.pivotCols[i]] = 1
  above_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      j.val < i.val → D.echelon[j][D.pivotCols[i]] = 0

end HexMatrix
