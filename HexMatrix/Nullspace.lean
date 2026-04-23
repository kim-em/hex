import HexMatrix.Span

/-!
Matrix-times-column-vector pairing for dense matrices.

The executable nullspace basis surface is deferred until it can be
implemented correctly. This module currently only provides the
column-vector multiplication helper used by downstream theorem
statements.
-/
namespace HexMatrix

universe u

open Lean.Grind

namespace Matrix

variable {R : Type u}

/--
Evaluate a dense matrix against a column vector.

This is the standard matrix-times-column-vector pairing used by the
nullspace scaffold.
-/
def mulVecRight [Zero R] [Add R] [Mul R] (M : Matrix R n m) (v : Vector R m) : Vector R n :=
  Vector.ofFn fun i => dot M[i] v

instance instHMulColVector [Zero R] [Add R] [Mul R] :
    HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVecRight

end Matrix

namespace IsRREF

variable {R : Type u} [Zero R] [One R] [Add R] [Mul R] [Neg R]
variable {n m : Nat} {M : Matrix R n m} {D : RowEchelonData R n m}

end IsRREF

end HexMatrix
