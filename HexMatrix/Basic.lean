/-!
Core dense matrix definitions for `hex-matrix`.

This module models matrices as `Vector (Vector R m) n` and provides the
basic executable operations needed by later linear-algebra algorithms:
row/column accessors, zero and identity matrices, dot products,
matrix-vector multiplication, matrix-matrix multiplication, and norm-squared
helpers.
-/
namespace Hex

universe u

/-- Dense `n × m` matrices over `R`, represented as vectors of rows. -/
abbrev Matrix (R : Type u) (n m : Nat) := Vector (Vector R m) n

namespace Vector

/-- Dot product of two vectors. -/
def dotProduct [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  (List.finRange n).foldl (fun acc i => acc + u[i] * v[i]) 0

/-- Squared Euclidean norm of a vector. -/
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  dotProduct v v

/-- Squared Euclidean norm specialized to integer vectors. -/
def intNormSq (v : Vector Int n) : Int :=
  normSq v

/-- Squared Euclidean norm specialized to rational vectors. -/
def ratNormSq (v : Vector Rat n) : Rat :=
  normSq v

end Vector

namespace Matrix

/-- Build a matrix from an entry function. -/
def ofFn (f : Fin n → Fin m → R) : Matrix R n m :=
  Vector.ofFn fun i => Vector.ofFn fun j => f i j

/-- The `i`-th row of a matrix. -/
def row (M : Matrix R n m) (i : Fin n) : Vector R m :=
  M[i]

/-- The `j`-th column of a matrix. -/
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Vector.ofFn fun i => M[i][j]

/-- The transpose of a dense matrix. -/
def transpose (M : Matrix R n m) : Matrix R m n :=
  Vector.ofFn fun j => col M j

/-- The all-zero matrix. -/
protected def zero [OfNat R 0] : Matrix R n m :=
  ofFn fun _ _ => 0

instance [OfNat R 0] : Zero (Matrix R n m) where
  zero := Matrix.zero

/-- The identity matrix. -/
protected def identity [OfNat R 0] [OfNat R 1] : Matrix R n n :=
  ofFn fun i j => if i = j then 1 else 0

instance [OfNat R 0] [OfNat R 1] : One (Matrix R n n) where
  one := Matrix.identity

/-- Dot product of two vectors. -/
def dot [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  Hex.Vector.dotProduct u v

/-- Multiply a matrix by a column vector. -/
def mulVec [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (v : Vector R m) :
    Vector R n :=
  Vector.ofFn fun i => dot (row M i) v

/-- Multiply two matrices. -/
def mul [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  ofFn fun i j => dot (row M i) (col N j)

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVec

instance [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Matrix R m k) (Matrix R n k) where
  hMul := mul

/-- Squared Euclidean norm of a vector. -/
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  Hex.Vector.normSq v

/-- Squared Euclidean norm specialized to integer vectors. -/
def intNormSq (v : Vector Int n) : Int :=
  Hex.Vector.intNormSq v

/-- Squared Euclidean norm specialized to rational vectors. -/
def ratNormSq (v : Vector Rat n) : Rat :=
  Hex.Vector.ratNormSq v

/-- Gram matrix of the rows of a dense matrix. -/
def gramMatrix [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) : Matrix R n n :=
  ofFn fun i j => Hex.Vector.dotProduct (row M i) (row M j)

/-- Leading principal `(k + 1) × (k + 1)` submatrix of a square matrix. -/
def submatrix (M : Matrix R n n) (k : Fin n) : Matrix R (k.val + 1) (k.val + 1) :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
    M[ii][jj]

end Matrix
end Hex
