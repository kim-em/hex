import HexGramSchmidt.Int

/-!
Executable Gram-determinant scaffolding for integer Gram-Schmidt data.

This module extends the initial integer-input `HexGramSchmidt` surface
with computable Gram determinants and scaled coefficients, together with
the adjacent theorem statements used by downstream lattice arguments.
-/

namespace Hex
namespace GramSchmidt
namespace Int

open HexMatrix

/-- The leading Gram matrix built from the first `k` rows of `b`. -/
def gramMatrix (b : HexMatrix.Matrix Int n m) (k : Nat) : HexMatrix.Matrix Int k k :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    HexMatrix.Matrix.dot (HexMatrix.Matrix.row b i.1) (HexMatrix.Matrix.row b j.1)

/--
The determinant witness for the scaled coefficient `ν[i,j]`, formed by
replacing the last column of the size-`j + 1` Gram matrix with inner
products against row `i`.
-/
def scaledCoeffMatrix (b : HexMatrix.Matrix Int n m) (i j : Nat) :
    HexMatrix.Matrix Int (j + 1) (j + 1) :=
  Vector.ofFn fun r => Vector.ofFn fun c =>
    let row := HexMatrix.Matrix.row b r.1
    let col :=
      if _h : c.1 < j then
        HexMatrix.Matrix.row b c.1
      else
        HexMatrix.Matrix.row b i
    HexMatrix.Matrix.dot row col

/--
The `k`-th Gram determinant. Phase 1 keeps this executable by taking the
determinant of the leading Gram matrix and exposing its natural-value
view.
-/
def gramDet (b : HexMatrix.Matrix Int n m) (k : Nat) (_hk : k ≤ n) : Nat :=
  if _hk0 : k = 0 then
    1
  else
    Int.toNat (HexMatrix.Matrix.det (gramMatrix b k))

/-- All leading Gram determinants, including the `d₀ = 1` convention. -/
def gramDetVec (b : HexMatrix.Matrix Int n m) : Vector Nat (n + 1) :=
  Vector.ofFn fun k => gramDet b k.1 (Nat.le_of_lt_succ k.2)

/-- Determinant-valued scaled coefficient entry. -/
def scaledCoeffEntry (b : HexMatrix.Matrix Int n m) (i j : Nat) : Int :=
  if _h : j < i then
    HexMatrix.Matrix.det (scaledCoeffMatrix b i j)
  else
    0

/--
Scaled Gram-Schmidt coefficients arranged as a lower-triangular integer
matrix.
-/
def scaledCoeffs (b : HexMatrix.Matrix Int n m) : HexMatrix.Matrix Int n n :=
  Vector.ofFn fun i => Vector.ofFn fun j => scaledCoeffEntry b i.1 j.1

/-- Temporary independence predicate for the scaffolded theorem layer. -/
def independent (_b : HexMatrix.Matrix Int n m) : Prop :=
  True

/-- Membership in the lattice spanned by the rows of `b`. -/
def memLattice (b : HexMatrix.Matrix Int n m) (v : Vector Int m) : Prop :=
  ∃ c : Vector Int n, b * c = v

/-- Product of the squared norms of the first `k` scaffolded basis rows. -/
noncomputable def basisNormSqProduct (b : HexMatrix.Matrix Int n m) (k : Nat) : Rat :=
  (List.range k).foldl
    (fun acc j => acc * HexMatrix.Vector.normSq (HexMatrix.Matrix.row (basis b) j))
    1

theorem gramDet_eq_prod_normSq (b : HexMatrix.Matrix Int n m)
    (_hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = basisNormSqProduct b k := by
  sorry

theorem gramDet_pos (b : HexMatrix.Matrix Int n m)
    (_hli : independent b) (k : Nat) (hk : k ≤ n) (_hk' : 0 < k) :
    0 < gramDet b k hk := by
  sorry

theorem basis_normSq (b : HexMatrix.Matrix Int n m)
    (_hli : independent b) (k : Nat) (hk : k < n) :
    HexMatrix.Vector.normSq (HexMatrix.Matrix.row (basis b) k) =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  sorry

theorem scaledCoeffs_eq (b : HexMatrix.Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    ((HexMatrix.Matrix.entry (scaledCoeffs b) i j : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        HexMatrix.Matrix.entry (coeffs b) i j := by
  sorry

theorem normSq_latticeVec_ge_min_basis_normSq
    (b : HexMatrix.Matrix Int n m) (_hli : independent b)
    (v : Vector Int m) (_hv : memLattice b v) (_hv' : v ≠ 0) :
    ∃ i, i < n ∧
      HexMatrix.Vector.normSq (HexMatrix.Matrix.row (basis b) i) ≤
        HexMatrix.Vector.normSq (castRow v) := by
  sorry

end Int
end GramSchmidt
end Hex
