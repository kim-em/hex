/-!
Nat-level extended GCD scaffolding.

This module provides the Phase 1 pure-`Nat` extended-GCD API and its
key correctness statements for the arithmetic library.
-/

namespace HexArith

/--
Compute the greatest common divisor of `a` and `b` together with
Bezout coefficients.
-/
def extGcd (a b : Nat) : Nat × Int × Int :=
  match b with
  | 0 => (a, 1, 0)
  | b' + 1 =>
      let (g, s, t) := extGcd (b' + 1) (a % (b' + 1))
      (g, t, s - t * Int.ofNat (a / (b' + 1)))
termination_by b
decreasing_by
  simp_wf
  exact Nat.mod_lt _ (Nat.succ_pos _)

theorem extGcd_fst (a b : Nat) : (extGcd a b).1 = Nat.gcd a b := by
  sorry

theorem extGcd_bezout (a b : Nat) :
    let (g, s, t) := extGcd a b
    s * a + t * b = g := by
  sorry

end HexArith
