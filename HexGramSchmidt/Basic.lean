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

private theorem dot_sub_smul_zero_of_dot_zero (row other basis : Vector Rat m) (c : Rat)
    (hrow : Matrix.dot row basis = 0) (hother : Matrix.dot other basis = 0) :
    Matrix.dot (row - c • other) basis = 0 := by
  rw [Matrix.dot_sub_smul_rat, hrow, hother]
  grind

private theorem dot_subtractProjection (row basisRow target : Vector Rat m) :
    Matrix.dot (subtractProjection row basisRow) target =
      Matrix.dot row target - projectionCoeff row basisRow * Matrix.dot basisRow target := by
  simp [subtractProjection, Matrix.dot_sub_smul_rat]

private theorem subtractProjection_add_projection (row basisRow : Vector Rat m) :
    row = subtractProjection row basisRow + projectionCoeff row basisRow • basisRow := by
  apply Vector.ext
  intro k hk
  change row[k] =
    (subtractProjection row basisRow + projectionCoeff row basisRow • basisRow)[k]
  rw [Vector.getElem_add, subtractProjection, Vector.getElem_sub, Vector.getElem_smul]
  grind

private theorem dot_subtractProjection_zero_of_dot_zero
    (row basisRow target : Vector Rat m)
    (hrow : Matrix.dot row target = 0) (hbasis : Matrix.dot basisRow target = 0) :
    Matrix.dot (subtractProjection row basisRow) target = 0 := by
  rw [dot_subtractProjection, hrow, hbasis]
  grind

private theorem dot_subtractProjection_self_zero (row basisRow : Vector Rat m)
    (hnorm : Matrix.dot basisRow basisRow ≠ 0) :
    Matrix.dot (subtractProjection row basisRow) basisRow = 0 := by
  rw [dot_subtractProjection]
  simp [projectionCoeff, hnorm]
  grind

private theorem rat_mul_self_nonneg (x : Rat) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using (Lean.Grind.OrderedRing.sq_nonneg (a := x))

private theorem rat_mul_self_eq_zero_of_nonpos (x : Rat) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := rat_mul_self_nonneg x
  have hsquare : x * x = 0 := by
    grind
  grind

private theorem foldl_dot_self_start_le (xs : List (Fin m)) (v : Vector Rat m)
    (acc : Rat) (hacc : 0 ≤ acc) :
    acc ≤ xs.foldl (fun sum i => sum + v[i] * v[i]) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hsq : 0 ≤ v[i] * v[i] := rat_mul_self_nonneg v[i]
      have hnext : 0 ≤ acc + v[i] * v[i] := by grind
      exact Rat.le_trans (by grind) (ih (acc := acc + v[i] * v[i]) hnext)

private theorem foldl_dot_self_eq_zero_of_mem (xs : List (Fin m)) (v : Vector Rat m)
    (acc : Rat) (hacc : 0 ≤ acc)
    (hzero : xs.foldl (fun sum i => sum + v[i] * v[i]) acc = 0) :
    ∀ i ∈ xs, v[i] = 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons head rest ih =>
      intro i hi
      simp only [List.mem_cons] at hi
      have hsq : 0 ≤ v[head] * v[head] := rat_mul_self_nonneg v[head]
      have hnext_nonneg : 0 ≤ acc + v[head] * v[head] := by grind
      have hnext_le_zero :
          acc + v[head] * v[head] ≤ 0 := by
        have hle :=
          foldl_dot_self_start_le (xs := rest) (v := v)
            (acc := acc + v[head] * v[head]) hnext_nonneg
        have hzero' :
            rest.foldl (fun sum i => sum + v[i] * v[i])
              (acc + v[head] * v[head]) = 0 := by
          simpa using hzero
        rw [hzero'] at hle
        exact hle
      have hnext_zero : acc + v[head] * v[head] = 0 := by grind
      have hhead_zero : v[head] = 0 := by
        apply rat_mul_self_eq_zero_of_nonpos
        grind
      cases hi with
      | inl h =>
          subst i
          exact hhead_zero
      | inr h =>
          exact ih (acc := acc + v[head] * v[head]) hnext_nonneg hzero i h

private theorem dot_self_eq_zero_get (v : Vector Rat m)
    (hzero : Matrix.dot v v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by
    simp
  exact foldl_dot_self_eq_zero_of_mem (xs := List.finRange m) (v := v)
    (acc := 0) (by decide) (by simpa [Matrix.dot, Hex.Vector.dotProduct] using hzero) i hmem

private theorem dot_zero_of_dot_self_zero (row v : Vector Rat m)
    (hzero : Matrix.dot v v = 0) :
    Matrix.dot row v = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [dot_self_eq_zero_get v hzero i]
      rw [show row[i] * (0 : Rat) = 0 by grind]
      rw [show (0 : Rat) + 0 = 0 by grind]
      change xs.foldl (fun acc i => acc + row[i] * v[i]) 0 = 0
      exact ih

private theorem dot_subtractProjection_self_zero_of_dot_self_zero
    (row basisRow : Vector Rat m)
    (hnorm : Matrix.dot basisRow basisRow = 0) :
    Matrix.dot (subtractProjection row basisRow) basisRow = 0 := by
  exact dot_zero_of_dot_self_zero (row := subtractProjection row basisRow)
    (v := basisRow) hnorm

private theorem foldl_dot_comm_rat (xs : List (Fin m)) (u v : Vector Rat m)
    (accU accV : Rat) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

private theorem dot_comm_rat (u v : Vector Rat m) :
    Matrix.dot u v = Matrix.dot v u := by
  simpa [Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_comm_rat (xs := List.finRange m) (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

private theorem projectionCoeff_subtractProjection_eq_of_dot_zero
    (row otherBasisRow basisRow : Vector Rat m)
    (horth : Matrix.dot otherBasisRow basisRow = 0) :
    projectionCoeff (subtractProjection row otherBasisRow) basisRow =
      projectionCoeff row basisRow := by
  by_cases hnorm : Matrix.dot basisRow basisRow = 0
  · simp [projectionCoeff, hnorm]
  · simp [projectionCoeff, dot_subtractProjection, horth, hnorm]
    grind

/-- Reduce a row against the previously constructed orthogonal basis rows. -/
private def reduceAgainstBasis (basisRev : List (Vector Rat m)) (row : Vector Rat m) :
    Vector Rat m :=
  basisRev.foldl subtractProjection row

private theorem dot_reduceAgainstBasis_zero_of_forall_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (horth : ∀ basisRow ∈ basisRev, Matrix.dot basisRow target = 0) :
    Matrix.dot (reduceAgainstBasis basisRev row) target = Matrix.dot row target := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      change Matrix.dot (reduceAgainstBasis rest (subtractProjection row basisRow)) target =
        Matrix.dot row target
      rw [ih]
      · rw [dot_subtractProjection, horth basisRow (by simp)]
        grind
      · intro laterBasisRow hlater
        exact horth laterBasisRow (by simp [hlater])

private theorem dot_reduceAgainstBasis_zero_of_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (hrow : Matrix.dot row target = 0)
    (horth : ∀ basisRow ∈ basisRev, Matrix.dot basisRow target = 0) :
    Matrix.dot (reduceAgainstBasis basisRev row) target = 0 := by
  rw [dot_reduceAgainstBasis_zero_of_forall_dot_zero basisRev row target horth, hrow]

private theorem dot_reduceAgainstBasis_of_mem
    (basisRev : List (Vector Rat m)) (row basisRow : Vector Rat m)
    (hmem : basisRow ∈ basisRev)
    (horth : basisRev.Pairwise (fun x y => Matrix.dot x y = 0 ∧ Matrix.dot y x = 0)) :
    Matrix.dot (reduceAgainstBasis basisRev row) basisRow = 0 := by
  induction basisRev generalizing row with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      by_cases hhead : head = basisRow
      · subst basisRow
        apply dot_reduceAgainstBasis_zero_of_dot_zero
        · by_cases hnorm : Matrix.dot head head = 0
          · exact dot_subtractProjection_self_zero_of_dot_self_zero row head hnorm
          · exact dot_subtractProjection_self_zero row head hnorm
        · intro later hlater
          exact (List.rel_of_pairwise_cons horth hlater).2
      · have htail : basisRow ∈ rest := by
          have hneq : basisRow ≠ head := by
            intro hb
            exact hhead hb.symm
          simp [hneq] at hmem
          exact hmem
        apply ih
        · exact htail
        · exact List.Pairwise.of_cons horth

private theorem projectionCoeff_reduceAgainstBasis_eq_of_forall_dot_zero
    (basisRev : List (Vector Rat m)) (row basisRow : Vector Rat m)
    (horth : ∀ otherBasisRow ∈ basisRev, Matrix.dot otherBasisRow basisRow = 0) :
    projectionCoeff (reduceAgainstBasis basisRev row) basisRow =
      projectionCoeff row basisRow := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons otherBasisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      change
        projectionCoeff (reduceAgainstBasis rest (subtractProjection row otherBasisRow)) basisRow =
          projectionCoeff row basisRow
      rw [ih]
      · exact projectionCoeff_subtractProjection_eq_of_dot_zero
          (row := row) (otherBasisRow := otherBasisRow) (basisRow := basisRow)
          (horth otherBasisRow (by simp))
      · intro laterBasisRow hlater
        exact horth laterBasisRow (by simp [hlater])

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

private theorem basisMatrix_reconstruction_invariant
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basisMatrix b).row ⟨i, hi⟩ +
        prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi := by
  sorry

end GramSchmidt

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
  simpa [basis, coeffs] using
    GramSchmidt.basisMatrix_reconstruction_invariant (b := b) i hi

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
  simpa [basis, coeffs, GramSchmidt.castIntMatrix, GramSchmidt.Rat.basis,
    GramSchmidt.Rat.coeffs, Matrix.row] using
      GramSchmidt.Rat.basis_decomposition (b := GramSchmidt.castIntMatrix b) i hi

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
end Hex
