import HexMatrix

/-!
Initial integer Gram-Schmidt scaffolding.

This module introduces the first `HexGramSchmidt` API slice for integer
input matrices: the rational Gram-Schmidt basis and coefficient matrix,
together with the immediate theorem surface used by downstream LLL work,
for the basis, coefficient, and decomposition contracts.
-/

namespace HexMatrix
namespace Matrix

universe u

variable {R : Type u} [Zero R]

/--
Nat-indexed row lookup for dense matrices.

The scaffold uses a zero row outside the matrix bounds so theorem
statements can follow the spec's Nat-indexed style.
-/
def row (M : Matrix R n m) (i : Nat) : Vector R m :=
  if h : i < n then M.get ⟨i, h⟩ else 0

/--
Nat-indexed entry lookup for dense matrices.

Out-of-bounds rows or columns return `0`, matching the row helper above.
-/
def entry (M : Matrix R n m) (i j : Nat) : R :=
  if hi : i < n then
    if hj : j < m then
      (M.get ⟨i, hi⟩).get ⟨j, hj⟩
    else
      0
  else
    0

end Matrix
end HexMatrix

namespace Hex
namespace GramSchmidt
namespace Int

open HexMatrix

/-- Cast an integer row to a rational row entrywise. -/
def castRow (v : Vector Int m) : Vector Rat m :=
  Vector.ofFn fun j => (v.get j : Rat)

/--
The Gram-Schmidt projection coefficient of `v` onto `w`.

For a zero vector `w`, this evaluates to `0` in `Rat`, matching the
field convention `0⁻¹ = 0`.
-/
noncomputable def projCoeff (v w : Vector Rat m) : Rat :=
  HexMatrix.Matrix.dot v w / HexMatrix.Matrix.dot w w

/--
The `i`-th Gram-Schmidt basis row for integer input, indexed by `Nat`.

Out-of-bounds indices evaluate against the zero input row, so the same
definition works for the theorem layer's Nat-indexed API.
-/
noncomputable def basisRow (b : HexMatrix.Matrix Int n m) (i : Nat) : Vector Rat m :=
  let v := castRow (HexMatrix.Matrix.row b i)
  let correction :=
    (List.finRange i).foldl
      (fun acc j =>
        let w := basisRow b j.1
        let μ := projCoeff v w
        Vector.ofFn fun k => acc.get k + μ * w.get k)
      0
  Vector.ofFn fun k => v.get k - correction.get k
termination_by i
decreasing_by
  exact j.2

/--
The integer-input Gram-Schmidt basis.
-/
noncomputable def basis (b : HexMatrix.Matrix Int n m) : HexMatrix.Matrix Rat n m :=
  Vector.ofFn fun i => basisRow b i.1

/--
The lower-unitriangular Gram-Schmidt coefficient matrix.
-/
noncomputable def coeffs (b : HexMatrix.Matrix Int n m) : HexMatrix.Matrix Rat n n :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    if _hji : j.1 < i.1 then
      projCoeff (castRow (HexMatrix.Matrix.row b i.1)) (basisRow b j.1)
    else if i = j then
      1
    else
      0

theorem basis_zero (b : HexMatrix.Matrix Int n m) (hn : 0 < n) :
    HexMatrix.Matrix.row (basis b) 0 = castRow (HexMatrix.Matrix.row b 0) := by
  sorry

theorem basis_orthogonal (b : HexMatrix.Matrix Int n m)
    (i j : Nat) (_hi : i < n) (_hj : j < n) (_hij : i ≠ j) :
    HexMatrix.Matrix.dot (HexMatrix.Matrix.row (basis b) i) (HexMatrix.Matrix.row (basis b) j) = 0 := by
  sorry

theorem basis_decomposition (b : HexMatrix.Matrix Int n m) (i : Nat) (_hi : i < n) :
    castRow (HexMatrix.Matrix.row b i) =
      HexMatrix.Matrix.row (basis b) i +
        (List.finRange i).foldl
          (fun acc (j : Fin i) =>
            acc + HexMatrix.Matrix.entry (coeffs b) i j.1 • HexMatrix.Matrix.row (basis b) j.1)
          0 := by
  sorry

theorem coeffs_diag (b : HexMatrix.Matrix Int n m) (i : Nat) (_hi : i < n) :
    HexMatrix.Matrix.entry (coeffs b) i i = 1 := by
  sorry

theorem coeffs_upper (b : HexMatrix.Matrix Int n m)
    (i j : Nat) (_hi : i < n) (_hj : j < n) (_hij : j > i) :
    HexMatrix.Matrix.entry (coeffs b) i j = 0 := by
  sorry

end Int
end GramSchmidt
end Hex
