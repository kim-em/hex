import HexMatrix

/-!
Initial integer Gram-Schmidt scaffolding.

This module introduces the first `HexGramSchmidt` API slice for integer
input matrices: the rational Gram-Schmidt basis and coefficient matrix,
together with the immediate theorem surface used by downstream LLL work,
including the prefix-span equivalence between input rows and basis rows.
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

/-- The Gram-Schmidt basis scaffold currently casts each input row to `Rat`. -/
noncomputable def basis (b : HexMatrix.Matrix Int n m) : HexMatrix.Matrix Rat n m :=
  Vector.ofFn fun i => castRow (b.get i)

/--
The Gram-Schmidt coefficient scaffold is currently the identity matrix,
giving the expected lower-unitriangular shape for the initial API slice.
-/
def coeffs (_b : HexMatrix.Matrix Int n m) : HexMatrix.Matrix Rat n n :=
  HexMatrix.Matrix.identity

/--
The first `k + 1` scaffolded Gram-Schmidt basis rows as a standalone
matrix, so prefix-span statements can use the existing row-span API.
-/
noncomputable def basisPrefix (b : HexMatrix.Matrix Int n m) (k : Nat) :
    HexMatrix.Matrix Rat (k + 1) m :=
  Vector.ofFn fun i => HexMatrix.Matrix.row (basis b) i.1

/--
The first `k + 1` input rows cast to `Rat`, packaged as a standalone
matrix for prefix-span statements.
-/
def inputPrefix (b : HexMatrix.Matrix Int n m) (k : Nat) :
    HexMatrix.Matrix Rat (k + 1) m :=
  Vector.ofFn fun i => castRow (HexMatrix.Matrix.row b i.1)

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

theorem basis_span (b : HexMatrix.Matrix Int n m) (i : Nat) (_hi : i < n)
    (v : Vector Rat m) :
    HexMatrix.Matrix.spanContains (basisPrefix b i) v =
      HexMatrix.Matrix.spanContains (inputPrefix b i) v := by
  sorry

end Int
end GramSchmidt
end Hex
