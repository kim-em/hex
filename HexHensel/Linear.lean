import HexHensel.Bridge

/-!
Executable linear Hensel-lifting scaffolding.

This module adds the first algorithmic boundary for `HexHensel`: the
single-step linear lift from a factorization modulo `p^k` to one modulo
`p^(k+1)`. The implementation stays computational and total, following
the spec's update shape while leaving the algebraic contract to theorem
statements for later phases.
-/

namespace HexHensel

open HexModArith
open HexPolyFp
open HexPolyZ

namespace ZPoly

/-- Coefficientwise quotient by `p^k` used in the linear Hensel error term. -/
def coeffwiseDivPow (f : ZPoly) (p k : Nat) : ZPoly :=
  let modulus := p ^ k
  if modulus = 0 then
    0
  else
    HexPoly.DensePoly.ofArray (R := Int) <|
      f.coeffs.map fun coeff => coeff / (modulus : Int)

/--
The `e` term from the linear Hensel update, computed by dividing the
current product error coefficientwise by `p^k`.
-/
def linearError (p k : Nat) (f g h : ZPoly) : ZPoly :=
  coeffwiseDivPow (f - g * h) p k

end ZPoly

/-- Result of one linear Hensel step. -/
structure LinearLiftResult where
  g : ZPoly
  h : ZPoly

namespace LinearLiftResult

/-- The factor product extracted from a linear-lift result. -/
def product (r : LinearLiftResult) : ZPoly :=
  r.g * r.h

end LinearLiftResult

/-- Multiply an integer polynomial by `p^k`. -/
private def scaleByPow (p k : Nat) (f : ZPoly) : ZPoly :=
  HexPoly.DensePoly.scaleInt (p ^ k : Int) f

/-- The lifted `delta g` correction term from the linear Hensel step. -/
private def linearDeltaG {p : Nat} [NeZero p] (g : ZPoly) (te : FpPoly p) : ZPoly :=
  let qr := HexPoly.DensePoly.divModMonic te (ZPoly.modP p g)
  FpPoly.liftToZ qr.remainder

/-- The lifted `delta h` correction term from the linear Hensel step. -/
private def linearDeltaH {p : Nat} [NeZero p]
    (g h : ZPoly) (s : FpPoly p) (te : FpPoly p) : ZPoly :=
  let qr := HexPoly.DensePoly.divModMonic te (ZPoly.modP p g)
  let correction := s * te + qr.quotient * ZPoly.modP p h
  FpPoly.liftToZ correction

/--
Executable linear Hensel lift from precision `p^k` to `p^(k+1)`.

The scaffold follows the spec-level update shape directly: compute the
coefficientwise error quotient, divide `t * e` by `g` modulo `p`, lift
the remainder and correction term back to `Z[x]`, then canonicalize the
updated factors modulo `p^(k+1)`.
-/
def linearHenselStep {p : Nat} [NeZero p]
    (k : Nat) (f g h : ZPoly) (s t : FpPoly p) : LinearLiftResult :=
  let eZ := ZPoly.linearError p k f g h
  let eFp := ZPoly.modP p eZ
  let te := t * eFp
  let deltaG := linearDeltaG g te
  let deltaH := linearDeltaH g h s te
  let g' := ZPoly.reduceModPow (g + scaleByPow p k deltaG) p (k + 1)
  let h' := ZPoly.reduceModPow (h + scaleByPow p k deltaH) p (k + 1)
  { g := g', h := h' }

/--
Linear Hensel step preserves the factorization modulo `p^(k+1)` under
the expected product, Bezout, and monicity hypotheses.
-/
theorem linearHenselStep_spec {p : Nat} [NeZero p]
    (k : Nat) (f g h : ZPoly) (s t : FpPoly p)
    (hprod : ZPoly.congr (g * h) f (p ^ k))
    (hbez : s * ZPoly.modP p g + t * ZPoly.modP p h = FpPoly.C (p := p) 1)
    (hmonic : HexPoly.DensePoly.Monic g) :
    ZPoly.congr (LinearLiftResult.product (linearHenselStep k f g h s t)) f (p ^ (k + 1)) := by
  sorry

end HexHensel
