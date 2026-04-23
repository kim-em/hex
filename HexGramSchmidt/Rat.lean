import HexMatrix

/-!
Initial rational Gram-Schmidt scaffolding.

This module introduces the Phase 1 `HexGramSchmidt` API slice for
rational input matrices: the rational Gram-Schmidt basis, coefficient
matrix, and Gram-determinant declarations used by downstream LLL work.
-/

namespace Hex
namespace GramSchmidt
namespace Rat

open HexMatrix

/--
Nat-indexed row lookup for rational-input dense matrices.

This matches the integer scaffold's convention of returning the zero row
outside the matrix bounds.
-/
def row (M : HexMatrix.Matrix Rat n m) (i : Nat) : Vector Rat m :=
  if h : i < n then M.get ⟨i, h⟩ else 0

/-- The rational-input Gram-Schmidt basis scaffold currently returns the input rows. -/
noncomputable def basis (b : HexMatrix.Matrix Rat n m) : HexMatrix.Matrix Rat n m :=
  b

/--
The rational-input coefficient scaffold is currently the identity
matrix, giving the expected lower-unitriangular shape for this API
slice.
-/
noncomputable def coeffs (_b : HexMatrix.Matrix Rat n m) : HexMatrix.Matrix Rat n n :=
  HexMatrix.Matrix.identity

/-- The leading Gram matrix built from the first `k` rows of `b`. -/
def gramMatrix (b : HexMatrix.Matrix Rat n m) (k : Nat) : HexMatrix.Matrix Rat k k :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    HexMatrix.Matrix.dot (row b i.1) (row b j.1)

/--
The `k`-th Gram determinant for a rational-input basis, computed from
the leading Gram matrix.
-/
def gramDet (b : HexMatrix.Matrix Rat n m) (k : Nat) (_hk : k ≤ n) : Rat :=
  if _hk0 : k = 0 then
    1
  else
    HexMatrix.Matrix.det (gramMatrix b k)

end Rat
end GramSchmidt
end Hex
