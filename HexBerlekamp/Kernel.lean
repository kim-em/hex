import HexBerlekamp.Matrix

/-!
Executable Berlekamp kernel-matrix scaffolding for `HexBerlekamp`.

This module adds the next Phase 1 boundary after the Berlekamp matrix:
the dense matrix `Q_f - I`. The theorem layer records its entrywise
meaning while the actual nullspace basis surface remains deferred until
`HexMatrix` grows a correct executable nullspace API.
-/

namespace HexBerlekamp

open HexModArith
open HexMatrix

variable {p : Nat} [NeZero p]

/--
Executable dense-matrix helper for `Q_f - I`, where `Q_f` is the
Berlekamp matrix of `f`.
-/
def berlekampKernelMatrix (f : HexPolyFp.FpPoly p) :
    Matrix (ZMod64 p) f.degree f.degree :=
  Vector.ofFn fun i =>
    Vector.ofFn fun j =>
      (berlekampMatrix (p := p) f)[i][j] - if i = j then 1 else 0

/--
Entry formula for the executable `Q_f - I` scaffold.
-/
theorem berlekampKernelMatrix_apply (f : HexPolyFp.FpPoly p) (i j : Fin f.degree) :
    (berlekampKernelMatrix (p := p) f)[i][j] =
      (berlekampMatrix (p := p) f)[i][j] - if i = j then 1 else 0 := by
  simp [berlekampKernelMatrix]

/-- Off-diagonal entries of `Q_f - I` agree with `Q_f`. -/
theorem berlekampKernelMatrix_apply_of_ne (f : HexPolyFp.FpPoly p)
    (i j : Fin f.degree) (hij : i ≠ j) :
    (berlekampKernelMatrix (p := p) f)[i][j] =
      (berlekampMatrix (p := p) f)[i][j] := by
  have hneg0 : -(0 : HexModArith.ZMod64 p) = 0 := by
    have h := HexModArith.ZMod64.neg_add_cancel (p := p) (a := (0 : HexModArith.ZMod64 p))
    rw [HexModArith.ZMod64.add_zero] at h
    exact h
  calc
    (berlekampKernelMatrix (p := p) f)[i][j]
        = (berlekampMatrix (p := p) f)[i][j] - 0 := by
            simpa [hij] using berlekampKernelMatrix_apply (p := p) f i j
    _ = (berlekampMatrix (p := p) f)[i][j] := by
      rw [HexModArith.ZMod64.sub_eq_add_neg]
      rw [hneg0]
      simpa using HexModArith.ZMod64.add_zero ((berlekampMatrix (p := p) f)[i][j])

/-- Diagonal entries of `Q_f - I` subtract `1` from the Berlekamp matrix. -/
theorem berlekampKernelMatrix_apply_diag (f : HexPolyFp.FpPoly p) (i : Fin f.degree) :
    (berlekampKernelMatrix (p := p) f)[i][i] =
      (berlekampMatrix (p := p) f)[i][i] - 1 := by
  simp [berlekampKernelMatrix]

end HexBerlekamp
