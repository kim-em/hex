import HexGramSchmidt.Basic
import HexMatrix.Determinant

/-!
Executable Gram-determinant and scaled-coefficient scaffolding for
`hex-gram-schmidt`.

This module adds the computable determinant-derived layer promised by the
specification. For integer inputs it exposes leading Gram determinants,
their vector packaging, and the integral scaled Gram-Schmidt coefficients
obtained from the Cramer-rule determinant formula. For rational inputs it
adds the analogous leading Gram determinants.
-/

namespace Hex

namespace GramSchmidt

/-- The leading `k × k` Gram submatrix, with `k` encoded as `j.val + 1`. -/
private def leadingGramSubmatrix {R : Type} [Mul R] [Add R] [OfNat R 0]
    (b : Matrix R n m) (j : Fin n) : Matrix R (j.val + 1) (j.val + 1) :=
  Matrix.submatrix (Matrix.gramMatrix b) j

/-- The Cramer-rule matrix whose determinant computes the scaled
Gram-Schmidt coefficient `ν[i,j]`. It is the leading `(j + 1) × (j + 1)`
Gram submatrix with its last column replaced by inner products with
`row i`. -/
private def scaledCoeffMatrix (b : Matrix Int n m) (i j : Fin n) :
    Matrix Int (j.val + 1) (j.val + 1) :=
  Matrix.ofFn fun r c =>
    let rr : Fin n := ⟨r.val, Nat.lt_of_lt_of_le r.isLt (Nat.succ_le_of_lt j.isLt)⟩
    if c.val = j.val then
      Hex.Vector.dotProduct (Matrix.row b rr) (Matrix.row b i)
    else
      let cc : Fin n := ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.succ_le_of_lt j.isLt)⟩
      Hex.Vector.dotProduct (Matrix.row b rr) (Matrix.row b cc)

end GramSchmidt

namespace GramSchmidt.Int

/-- Integer-valued helper for the `k`-th Gram determinant. -/
def gramDetInt (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Int :=
  match k with
  | 0 => 1
  | k' + 1 =>
      Matrix.det (GramSchmidt.leadingGramSubmatrix b ⟨k', Nat.lt_of_succ_le hk⟩)

/-- The `k`-th Gram determinant: determinant of the `k × k` leading Gram
submatrix, returned as a natural number with `gramDet b 0 = 1`. -/
def gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Nat :=
  (gramDetInt b k hk).toNat

/-- All leading Gram determinants, from `k = 0` through `k = n`. -/
def gramDetVec (b : Matrix Int n m) : Vector Nat (n + 1) :=
  Vector.ofFn fun i => gramDet b i.val (Nat.le_of_lt_succ i.isLt)

/-- The scaled Gram-Schmidt coefficients (`ν`-values), expressed as the
integral determinants from the Cramer-rule formula. Entries on and above
the diagonal are set to `0`. -/
def scaledCoeffs (b : Matrix Int n m) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if j.val < i.val then
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j)
    else
      0

theorem gramDetInt_zero (b : Matrix Int n m) :
    gramDetInt b 0 (Nat.zero_le n) = 1 := rfl

theorem gramDet_zero (b : Matrix Int n m) :
    gramDet b 0 (Nat.zero_le n) = 1 := rfl

theorem gramDetInt_succ (b : Matrix Int n m) (k : Nat) (hk : k + 1 ≤ n) :
    gramDetInt b (k + 1) hk =
      Matrix.det (GramSchmidt.leadingGramSubmatrix b ⟨k, Nat.lt_of_succ_le hk⟩) := rfl

theorem gramDet_succ (b : Matrix Int n m) (k : Nat) (hk : k + 1 ≤ n) :
    gramDet b (k + 1) hk =
      (Matrix.det (GramSchmidt.leadingGramSubmatrix b ⟨k, Nat.lt_of_succ_le hk⟩)).toNat := rfl

theorem gramDetVec_zero (b : Matrix Int n m) :
    (gramDetVec b).get ⟨0, Nat.succ_pos n⟩ = 1 := by
  sorry

theorem gramDetVec_succ (b : Matrix Int n m) (k : Fin n) :
    (gramDetVec b).get ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ =
      gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) := by
  sorry

theorem scaledCoeffs_eq_det (b : Matrix Int n m) (i j : Fin n) (hij : j < i) :
    GramSchmidt.entry (scaledCoeffs b) i j = Matrix.det (GramSchmidt.scaledCoeffMatrix b i j) := by
  sorry

theorem scaledCoeffs_upper (b : Matrix Int n m) (i j : Fin n) (hij : i ≤ j) :
    GramSchmidt.entry (scaledCoeffs b) i j = 0 := by
  sorry

theorem scaledCoeffs_eq (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    let ii : Fin n := ⟨i, hi⟩
    let jj : Fin n := ⟨j, Nat.lt_trans hj hi⟩
    ((GramSchmidt.entry (scaledCoeffs b) ii jj : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ii jj := by
  sorry

end GramSchmidt.Int

namespace GramSchmidt.Rat

/-- The `k`-th Gram determinant for a rational basis. -/
def gramDet (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Rat :=
  match k with
  | 0 => 1
  | k' + 1 =>
      Matrix.det (GramSchmidt.leadingGramSubmatrix b ⟨k', Nat.lt_of_succ_le hk⟩)

theorem gramDet_zero (b : Matrix Rat n m) :
    gramDet b 0 (Nat.zero_le n) = 1 := rfl

theorem gramDet_succ (b : Matrix Rat n m) (k : Nat) (hk : k + 1 ≤ n) :
    gramDet b (k + 1) hk =
      Matrix.det (GramSchmidt.leadingGramSubmatrix b ⟨k, Nat.lt_of_succ_le hk⟩) := rfl

end GramSchmidt.Rat

end Hex
