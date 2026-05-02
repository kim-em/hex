import HexMatrix.RREF

/-!
Core Gram-Schmidt basis and coefficient definitions for `hex-gram-schmidt`.

This module provides executable Gram-Schmidt basis and coefficient
constructions over the dense `Hex.Matrix` representation. Integer inputs are
cast to rationals before applying Gram-Schmidt; rational inputs operate
directly on the ambient matrix. It also states the structural theorems used by
downstream lattice and reduction code, including the prefix-span invariance
surface consumed by later LLL work.
-/
namespace Hex

namespace GramSchmidt

/-- Coefficient of the orthogonal projection of `row` onto `basisRow`.
When the basis row has zero norm we use `0`, which matches the degenerate
case of Gram-Schmidt where the corresponding projection term vanishes. -/
private def projectionCoeff (row basisRow : Vector Rat m) : Rat :=
  let denom := Matrix.dot basisRow basisRow
  if denom = 0 then 0 else Matrix.dot row basisRow / denom

/-- Subtract the projection of `row` onto `basisRow`. -/
private def subtractProjection (row basisRow : Vector Rat m) : Vector Rat m :=
  row - projectionCoeff row basisRow • basisRow

/-- Reduce a row against the previously constructed orthogonal basis rows. -/
private def reduceAgainstBasis (basisRev : List (Vector Rat m)) (row : Vector Rat m) :
    Vector Rat m :=
  basisRev.foldl subtractProjection row

/-- Left-to-right Gram-Schmidt orthogonalization on a list of rows. -/
private def basisRowsAux (basisRev pending : List (Vector Rat m)) : List (Vector Rat m) :=
  match pending with
  | [] => basisRev.reverse
  | row :: rows =>
      let next := reduceAgainstBasis basisRev row
      basisRowsAux (next :: basisRev) rows

/-- Left-to-right Gram-Schmidt orthogonalization on a matrix's rows. -/
private def basisRows (rows : List (Vector Rat m)) : List (Vector Rat m) :=
  basisRowsAux [] rows

/-- Rebuild a matrix from its row list after Gram-Schmidt orthogonalization. -/
private def basisMatrix (b : Matrix Rat n m) : Matrix Rat n m :=
  let rows := basisRows b.toList
  Vector.ofFn fun i => rows[i.val]!

private theorem basisRowsAux_reverse_prefix (basisRev pending : List (Vector Rat m)) :
    ∃ suffix, basisRowsAux basisRev pending = basisRev.reverse ++ suffix := by
  induction pending generalizing basisRev with
  | nil =>
      exact ⟨[], by simp [basisRowsAux]⟩
  | cons row rows ih =>
      obtain ⟨suffix, hsuffix⟩ :=
        ih (GramSchmidt.reduceAgainstBasis basisRev row :: basisRev)
      refine ⟨GramSchmidt.reduceAgainstBasis basisRev row :: suffix, ?_⟩
      simp [basisRowsAux, hsuffix, List.reverse_cons, List.append_assoc]

private theorem basisRowsAux_singleton_head (row : Vector Rat m) (rows : List (Vector Rat m)) :
    (basisRowsAux [row] rows)[0]! = row := by
  obtain ⟨suffix, hsuffix⟩ := basisRowsAux_reverse_prefix [row] rows
  simp [hsuffix]

private theorem basisRows_head (b : Matrix Rat n m) (hn : 0 < n) :
    (basisRows b.toList)[0]! = b[0] := by
  have hlen : b.toList.length = n := by simp
  cases hrows : b.toList with
  | nil =>
      simp [hrows] at hlen
      omega
  | cons row rows =>
      have hrow : row = b[0] := by
        have hget := Vector.getElem_toList (xs := b) (i := 0) (h := by simpa [hlen] using hn)
        simpa [hrows] using hget
      simpa [basisRows, basisRowsAux, reduceAgainstBasis, hrows, hrow] using
        basisRowsAux_singleton_head (row := b[0]) (rows := rows)

/-- Gram-Schmidt coefficient matrix for an already-cast rational input. -/
private def coeffMatrix (rows basis : Matrix Rat n m) : Matrix Rat n n :=
  Matrix.ofFn fun i j =>
    if hlt : j.val < i.val then
      projectionCoeff rows[i] basis[j]
    else if i = j then
      1
    else
      0

/-- Access a dense matrix entry by row and column indices. -/
def entry (M : Matrix R n m) (i : Fin n) (j : Fin m) : R :=
  (M.row i)[j]

/-- Cast an integer matrix into the rational matrix space used by
Gram-Schmidt. -/
private def castIntMatrix (b : Matrix Int n m) : Matrix Rat n m :=
  Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b

/-- The prefix combination term used in the decomposition theorem shape. -/
def prefixCombination (coeffs : Matrix Rat n n) (basis : Matrix Rat n m) (i : Nat) (hi : i < n) :
    Vector Rat m :=
  (List.finRange i).foldl
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_trans j.isLt hi⟩
      acc + GramSchmidt.entry coeffs ⟨i, hi⟩ jn • basis.row jn)
    0

/-- The row-prefix matrix containing rows `0` through `i`. -/
def prefixRows (M : Matrix R n m) (i : Nat) (hi : i < n) : Matrix R (i + 1) m :=
  Vector.ofFn fun j => M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩

/-- Executable row-span membership in the first `i + 1` rows of a matrix. -/
def prefixSpan (M : Matrix Rat n m) (i : Nat) (hi : i < n) (v : Vector Rat m) : Prop :=
  ∃ c : Vector Rat (i + 1), Matrix.rowCombination (prefixRows M i hi) c = v

private theorem entry_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    entry (Matrix.ofFn f) i j = f i j := by
  simp [entry, Matrix.row, Matrix.ofFn, Vector.getElem_ofFn]

end GramSchmidt

namespace GramSchmidt.Int

/-- The Gram-Schmidt orthogonal basis for an integer matrix, viewed in
`Rat` after coefficient divisions. -/
noncomputable def basis (b : Matrix Int n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix (GramSchmidt.castIntMatrix b)

/-- The Gram-Schmidt coefficient matrix for an integer input matrix. -/
noncomputable def coeffs (b : Matrix Int n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix (GramSchmidt.castIntMatrix b) (basis b)

theorem basis_zero (b : Matrix Int n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ =
      Vector.map (fun x : Int => (x : Rat)) (b.row ⟨0, hn⟩) := by
  simpa [basis, GramSchmidt.basisMatrix, GramSchmidt.castIntMatrix, Matrix.row] using
    GramSchmidt.basisRows_head (b := GramSchmidt.castIntMatrix b) hn

theorem basis_orthogonal (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Matrix.dot ((basis b).row ⟨i, hi⟩) ((basis b).row ⟨j, hj⟩) = 0 := by
  sorry

theorem basis_decomposition (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    Vector.map (fun x : Int => (x : Rat)) (b.row ⟨i, hi⟩) =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  sorry

theorem coeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]

theorem coeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]

theorem basis_span (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan (GramSchmidt.castIntMatrix b) i hi v := by
  sorry

end GramSchmidt.Int

namespace GramSchmidt.Rat

/-- The Gram-Schmidt orthogonal basis for a rational matrix. -/
noncomputable def basis (b : Matrix Rat n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix b

/-- The Gram-Schmidt coefficient matrix for a rational input matrix. -/
noncomputable def coeffs (b : Matrix Rat n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix b (basis b)

theorem basis_zero (b : Matrix Rat n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ = b.row ⟨0, hn⟩ := by
  simpa [basis, GramSchmidt.basisMatrix, Matrix.row] using
    GramSchmidt.basisRows_head (b := b) hn

theorem basis_orthogonal (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Matrix.dot ((basis b).row ⟨i, hi⟩) ((basis b).row ⟨j, hj⟩) = 0 := by
  sorry

theorem basis_decomposition (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  sorry

theorem coeffs_diag (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn]

theorem coeffs_upper (b : Matrix Rat n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  have hnot_lt : ¬j < i := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  simp [coeffs, GramSchmidt.coeffMatrix, GramSchmidt.entry_ofFn, hnot_lt, hne]

theorem basis_span (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan b i hi v := by
  sorry

end GramSchmidt.Rat
end Hex
