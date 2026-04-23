import HexMatrix.Rref

/-!
Span-membership scaffolding for dense matrices.

This module introduces the Phase 1 API surface for computing row-span
coefficients and testing row-span membership via existing echelon-form
data.
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

namespace IsEchelonForm

variable {R : Type u} [Zero R] [One R] [Add R] [Mul R]
variable {n m : Nat} {M : Matrix R n m} {D : RowEchelonData R n m}

/--
Temporary Phase 1 scaffold for recovering row-span coefficients from an
echelon witness.
-/
def spanCoeffs (_E : IsEchelonForm M D) (_v : Vector R m) : Option (Vector R n) :=
  if _h : D.rank = 0 then
    some 0
  else
    none

/-- Temporary Phase 1 scaffold for row-span membership. -/
def spanContains (E : IsEchelonForm M D) (v : Vector R m) : Bool :=
  (E.spanCoeffs v).isSome

theorem spanCoeffs_sound (E : IsEchelonForm M D) (v : Vector R m) (c : Vector R n) :
    E.spanCoeffs v = some c → M * c = v := by
  sorry

theorem spanCoeffs_complete (E : IsEchelonForm M D) (v : Vector R m) :
    (∃ c : Vector R n, M * c = v) → (E.spanCoeffs v).isSome := by
  sorry

theorem spanContains_iff (E : IsEchelonForm M D) (v : Vector R m) :
    E.spanContains v = true ↔ ∃ c : Vector R n, M * c = v := by
  sorry

end IsEchelonForm

/--
Convenience wrapper for row-span coefficients.

Phase 1 keeps this executable while the row-reduction convenience path is
still being scaffolded in separate issues.
-/
def Matrix.spanCoeffs {R : Type u} [Zero R] [One R] [Add R] [Mul R] {n m : Nat}
    (_M : Matrix R n m) (_v : Vector R m) : Option (Vector R n) :=
  none

/-- Convenience wrapper: test span membership through the scaffolded RREF. -/
def Matrix.spanContains {R : Type u} [Zero R] [One R] [Add R] [Mul R] {n m : Nat}
    (M : Matrix R n m) (v : Vector R m) : Bool :=
  (Matrix.spanCoeffs M v).isSome

end HexMatrix
