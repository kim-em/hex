/-!
Extended GCD scaffolding.

This module provides the Phase 1 pure-`Nat` extended-GCD API together
with the pure/public `UInt64` surface promised by the arithmetic SPEC.
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

namespace Hex

/--
Pure-Lean `UInt64` extended GCD reference implementation.

The scaffold computes the coefficients through the `Nat` implementation
and repackages the gcd into a machine word.
-/
def pureUInt64ExtGcd (a b : UInt64) : UInt64 × Int × Int :=
  let (g, s, t) := HexArith.extGcd a.toNat b.toNat
  (.ofNat g, s, t)

end Hex

namespace HexArith

namespace UInt64

/-- Public `UInt64` extended GCD API surface. -/
def extGcd (a b : UInt64) : UInt64 × Int × Int :=
  Hex.pureUInt64ExtGcd a b

theorem extGcd_fst (a b : UInt64) :
    (extGcd a b).1.toNat = Nat.gcd a.toNat b.toNat := by
  sorry

theorem extGcd_bezout (a b : UInt64) :
    let (g, s, t) := extGcd a b
    s * Int.ofNat a.toNat + t * Int.ofNat b.toNat = Int.ofNat g.toNat := by
  sorry

end UInt64

end HexArith
