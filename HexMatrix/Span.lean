import HexMatrix.Rref

/-!
Row-combination helpers for dense matrices.

This module provides the executable matrix-times-coefficient-vector
pairing used by theorem statements that speak about linear combinations
of matrix rows.
-/
namespace HexMatrix

universe u

namespace Matrix

variable {R : Type u}

/--
Evaluate a coefficient vector against the rows of a dense matrix.

This is the row-span pairing used by the span scaffold: `M * c` is the
linear combination of the rows of `M` with coefficients `c`.
-/
def mulVec [Zero R] [Add R] [Mul R] (M : Matrix R n m) (c : Vector R n) : Vector R m :=
  Vector.ofFn fun j =>
    (List.finRange n).foldl (fun acc i => acc + c[i] * M[i][j]) 0

instance instHMulVector [Zero R] [Add R] [Mul R] :
    HMul (Matrix R n m) (Vector R n) (Vector R m) where
  hMul := mulVec

end Matrix

end HexMatrix
