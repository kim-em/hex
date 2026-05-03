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

private theorem foldl_dotProduct_sub_smul_rat
    (xs : List (Fin n)) (u v w : Vector Rat n) (c accU accV : Rat) :
    xs.foldl (fun acc i => acc + (u - c • v)[i] * w[i]) (accU - c * accV) =
      xs.foldl (fun acc i => acc + u[i] * w[i]) accU -
        c * xs.foldl (fun acc i => acc + v[i] * w[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons i xs ih =>
      have hstart :
          accU - c * accV + (u - c • v)[i] * w[i] =
            (accU + u[i] * w[i]) - c * (accV + v[i] * w[i]) := by
        have hentry : (u - c • v)[i] = u[i] - c * v[i] := by
          change (u - c • v)[i.val] = u[i.val] - c * v[i.val]
          rw [Vector.getElem_sub, Vector.getElem_smul]
          rfl
        rw [hentry]
        grind
      simp only [List.foldl_cons]
      rw [hstart]
      exact ih (accU := accU + u[i] * w[i]) (accV := accV + v[i] * w[i])

/-- Dot product distributes over subtracting a scalar multiple in the left argument. -/
theorem dotProduct_sub_smul_rat (u v w : Vector Rat n) (c : Rat) :
    dotProduct (u - c • v) w = dotProduct u w - c * dotProduct v w := by
  have hzero : (0 : Rat) - 0 = 0 := by
    grind
  simpa [dotProduct, hzero] using
    foldl_dotProduct_sub_smul_rat (xs := List.finRange n) (u := u) (v := v) (w := w)
      (c := c) (accU := 0) (accV := 0)

/-- Zero specialization of `dotProduct_sub_smul`. -/
theorem dotProduct_sub_smul_eq_zero_rat (u v w : Vector Rat n) (c : Rat)
    (h : dotProduct u w = c * dotProduct v w) :
    dotProduct (u - c • v) w = 0 := by
  rw [dotProduct_sub_smul_rat, h]
  grind

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

/-- Dot product distributes over subtracting a scalar multiple in the left argument. -/
theorem dot_sub_smul_rat (u v w : Vector Rat n) (c : Rat) :
    dot (u - c • v) w = dot u w - c * dot v w := by
  simpa [dot] using Hex.Vector.dotProduct_sub_smul_rat (u := u) (v := v) (w := w) (c := c)

/-- Zero specialization of `dot_sub_smul`. -/
theorem dot_sub_smul_eq_zero_rat (u v w : Vector Rat n) (c : Rat)
    (h : dot u w = c * dot v w) :
    dot (u - c • v) w = 0 := by
  rw [dot_sub_smul_rat, h]
  grind

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

/-- Leading principal `k × k` prefix of a square matrix. This variant includes
the empty prefix and is convenient for Bareiss pivot/minor statements. -/
def leadingPrefix (M : Matrix R n n) (k : Nat) (hk : k ≤ n) : Matrix R k k :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[ii][jj]

@[simp] theorem leadingPrefix_entry (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (leadingPrefix M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]) := by
  simp [leadingPrefix, ofFn]

@[simp] theorem submatrix_entry (M : Matrix R n n) (k : Fin n)
    (i j : Fin (k.val + 1)) :
    (submatrix M k)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt k.isLt)⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
       M[ii][jj]) := by
  simp [submatrix, ofFn]

/-- The existing `submatrix` API is the `(k + 1)` leading-prefix API at the
same boundary. -/
theorem submatrix_eq_leadingPrefix (M : Matrix R n n) (k : Fin n) :
    submatrix M k = leadingPrefix M (k.val + 1) (Nat.succ_le_of_lt k.isLt) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [submatrix, leadingPrefix, ofFn]

/-- Bordered Bareiss minor with the first `k` rows/columns and one extra
border row `i` and column `j`. For Bareiss applications `i` and `j` are in the
trailing part, but the constructor is total and leaves that side condition to
the invariant using it. -/
def borderedMinor (M : Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    Matrix R (k + 1) (k + 1) :=
  ofFn fun r c =>
    let rr : Fin n :=
      if hr : r.val < k then
        ⟨r.val, Nat.lt_trans hr hk⟩
      else
        i
    let cc : Fin n :=
      if hc : c.val < k then
        ⟨c.val, Nat.lt_trans hc hk⟩
      else
        j
    M[rr][cc]

@[simp] theorem borderedMinor_entry_lt_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r c : Fin (k + 1)) (hr : r.val < k) (hc : c.val < k) :
    (borderedMinor M k hk i j)[r][c] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[rr][cc]) := by
  simp [borderedMinor, ofFn, hr, hc]

@[simp] theorem borderedMinor_entry_lt_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r : Fin (k + 1)) (hr : r.val < k) :
    (borderedMinor M k hk i j)[r][Fin.last k] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       M[rr][j]) := by
  simp [borderedMinor, ofFn, hr]

@[simp] theorem borderedMinor_entry_last_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (c : Fin (k + 1)) (hc : c.val < k) :
    (borderedMinor M k hk i j)[Fin.last k][c] =
      (let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[i][cc]) := by
  simp [borderedMinor, ofFn, hc]

@[simp] theorem borderedMinor_entry_last_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) :
    (borderedMinor M k hk i j)[Fin.last k][Fin.last k] = M[i][j] := by
  simp [borderedMinor, ofFn]

end Matrix
end Hex
