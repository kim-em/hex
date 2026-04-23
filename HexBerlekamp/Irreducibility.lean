import HexBerlekamp.Kernel

/-!
Executable irreducibility-rank scaffolding for `HexBerlekamp`.

This module packages the next public Phase 1 boundary after the
Berlekamp-kernel scaffold: the rank of `Q_f - I` and the corresponding
executable irreducibility test predicted by Berlekamp's criterion.
The implementation stays at the `berlekampKernelMatrix` / `rref`
boundary so later phases can refine the algebraic correctness story
without changing the public executable surface introduced here.
-/

namespace HexBerlekamp

open HexModArith
open HexMatrix

variable {p : Nat} [NeZero p]

section WithField

variable (hField : Lean.Grind.Field (HexModArith.ZMod64 p))

/--
Executable rank of the Berlekamp kernel matrix `Q_f - I`.
-/
def berlekampKernelRank (f : HexPolyFp.FpPoly p) : Nat :=
  let _ : Lean.Grind.Field (HexModArith.ZMod64 p) := hField
  (rref (berlekampKernelMatrix (p := p) f)).rank

/--
Proposition-level form of Berlekamp's irreducibility criterion.
-/
def irreducibleByRank (f : HexPolyFp.FpPoly p) : Prop :=
  berlekampKernelRank (p := p) (hField := hField) f = f.degree - 1

instance instDecidableIrreducibleByRank (f : HexPolyFp.FpPoly p) :
    Decidable (irreducibleByRank (p := p) (hField := hField) f) := by
  unfold irreducibleByRank
  infer_instance

/--
Executable boolean test for the scaffolded Berlekamp rank criterion.
-/
def berlekampIrreducible? (f : HexPolyFp.FpPoly p) : Bool :=
  berlekampKernelRank (p := p) (hField := hField) f == f.degree - 1

/-- The kernel-rank helper is exactly the rank reported by `rref (Q_f - I)`. -/
theorem berlekampKernelRank_eq_rref_rank (f : HexPolyFp.FpPoly p) :
    berlekampKernelRank (p := p) (hField := hField) f =
      (rref (berlekampKernelMatrix (p := p) f)).rank := by
  simp [berlekampKernelRank]

/-- The proposition-level scaffold unfolds to the advertised `rank(Q_f - I) = n - 1` test. -/
theorem irreducibleByRank_iff (f : HexPolyFp.FpPoly p) :
    irreducibleByRank (p := p) (hField := hField) f ↔
      (rref (berlekampKernelMatrix (p := p) f)).rank = f.degree - 1 := by
  simp [irreducibleByRank, berlekampKernelRank]

/-- The boolean irreducibility test agrees with the rank criterion. -/
theorem berlekampIrreducible?_eq_true_iff (f : HexPolyFp.FpPoly p) :
    berlekampIrreducible? (p := p) (hField := hField) f = true ↔
      (rref (berlekampKernelMatrix (p := p) f)).rank = f.degree - 1 := by
  simp [berlekampIrreducible?, berlekampKernelRank]

/-- A successful boolean check certifies the expected `Q_f - I` rank equation. -/
theorem berlekampIrreducible?_sound (f : HexPolyFp.FpPoly p) :
    berlekampIrreducible? (p := p) (hField := hField) f = true →
      (rref (berlekampKernelMatrix (p := p) f)).rank = f.degree - 1 := by
  intro h
  exact (berlekampIrreducible?_eq_true_iff (p := p) (hField := hField) f).1 h

/-- The boolean test is the decidable reflection of the proposition-level scaffold. -/
theorem berlekampIrreducible?_eq_decide (f : HexPolyFp.FpPoly p) :
    berlekampIrreducible? (p := p) (hField := hField) f =
      decide (irreducibleByRank (p := p) (hField := hField) f) := by
  by_cases hEq : berlekampKernelRank (p := p) (hField := hField) f = f.degree - 1
  · simp [berlekampIrreducible?, irreducibleByRank, hEq]
  · simp [berlekampIrreducible?, irreducibleByRank, hEq]

end WithField

end HexBerlekamp
