import HexHensel.Linear

/-!
Executable iterative Hensel-lift scaffolding.

This module packages the public `henselLift` wrapper promised by the
`hex-hensel` specification. It iterates the existing linear step from an
initial factorization modulo `p`, keeping the API total and computational
while recording the intended precision contract as theorem statements for
later phases.
-/

namespace HexHensel

open HexPolyFp
open HexPolyZ

/--
Number of linear refinement steps needed to reach the public precision
target `p^k` when the input factorization already starts modulo `p`.
-/
def henselLiftStepCount (k : Nat) : Nat :=
  k - 1

/--
Canonicalize the initial `mod p` input factors before iterative lifting.
-/
def henselLiftBase {p : Nat} [NeZero p] (g h : ZPoly) : LinearLiftResult :=
  { g := ZPoly.reduceModPow g p 1
    h := ZPoly.reduceModPow h p 1 }

/--
Iterate the linear Hensel step from current precision `p^precision` for a
given number of remaining refinements.
-/
def henselLiftAux {p : Nat} [NeZero p]
    (precision : Nat) (f : ZPoly) (s t : FpPoly p) : Nat → LinearLiftResult → LinearLiftResult
  | 0, acc => acc
  | steps + 1, acc =>
      henselLiftAux (precision + 1) f s t steps (linearHenselStep precision f acc.g acc.h s t)

/--
Public iterative Hensel-lift wrapper producing factors intended to be
valid modulo `p^k`.
-/
def henselLift {p : Nat} [NeZero p]
    (k : Nat) (f g h : ZPoly) (s t : FpPoly p) : LinearLiftResult :=
  henselLiftAux (p := p) 1 f s t (henselLiftStepCount k) (henselLiftBase (p := p) g h)

/--
If the initial factors are valid modulo `p`, iterating the linear step to
precision `k` preserves the factorization modulo `p^k`.
-/
theorem henselLift_spec {p : Nat} [NeZero p]
    (k : Nat) (hk : 1 ≤ k) (f g h : ZPoly) (s t : FpPoly p)
    (hprod : ZPoly.congr (g * h) f p)
    (hbez : s * ZPoly.modP p g + t * ZPoly.modP p h = FpPoly.C (p := p) 1)
    (hmonic : HexPoly.DensePoly.Monic g) :
    ZPoly.congr (LinearLiftResult.product (henselLift k f g h s t)) f (p ^ k) := by
  sorry

end HexHensel
