import HexBerlekamp.Matrix

/-!
Executable Berlekamp-kernel scaffolding for `HexBerlekamp`.

This module adds the next Phase 1 boundary after the Berlekamp matrix:
the dense matrix `Q_f - I` and the corresponding nullspace basis routed
through the existing `HexMatrix` scaffold. The theorem layer records the
entrywise meaning of `Q_f - I` and the immediate soundness contract that
each returned basis vector lies in the kernel.
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

section WithField

variable (hField : Lean.Grind.Field (HexModArith.ZMod64 p))

/--
Executable Berlekamp-kernel basis for `f`, routed through the shared
`HexMatrix` nullspace scaffold on `Q_f - I`.
-/
def berlekampKernel (f : HexPolyFp.FpPoly p) :
    Vector (Vector (HexModArith.ZMod64 p) f.degree)
      (f.degree - (rref (berlekampKernelMatrix (p := p) f)).rank) :=
  let _ : Lean.Grind.Field (HexModArith.ZMod64 p) := hField
  Matrix.nullspace (berlekampKernelMatrix (p := p) f)

/--
Every scaffolded Berlekamp-kernel basis vector is annihilated by
`Q_f - I`.
-/
theorem berlekampKernel_sound (f : HexPolyFp.FpPoly p)
    (k : Fin (f.degree - (rref (berlekampKernelMatrix (p := p) f)).rank)) :
    berlekampKernelMatrix (p := p) f * (berlekampKernel (p := p) (hField := hField) f)[k] =
      Vector.replicate f.degree
        (HexModArith.ZMod64.zero p (Nat.pos_of_ne_zero (NeZero.ne p))) := by
  sorry

end WithField

end HexBerlekamp
