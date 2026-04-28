/-!
Extended GCD algorithms and specifications.

This module defines pure-`Nat`, `Int`, and `UInt64` extended-GCD
operations together with the core gcd and Bezout-certificate theorems
used by the arithmetic library.
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

This remains available as a proof/reference helper. The public runtime
`HexArith.UInt64.extGcd` API delegates through `HexArith.Int.extGcd`.
-/
def pureUInt64ExtGcd (a b : UInt64) : UInt64 × Int × Int :=
  let (g, s, t) := HexArith.extGcd a.toNat b.toNat
  (.ofNat g, s, t)

/--
Pure Lean reference implementation of extended GCD over integers.

The computation reduces to the `Nat` variant on absolute values and then
re-signs the Bezout coefficients to match the original inputs.
-/
def pureIntExtGcd (a b : Int) : Nat × Int × Int :=
  let (g, s, t) := HexArith.extGcd a.natAbs b.natAbs
  let s' := if a < 0 then -s else s
  let t' := if b < 0 then -t else t
  (g, s', t')

theorem pureIntExtGcd_fst (a b : Int) :
    (pureIntExtGcd a b).1 = Int.gcd a b := by
  sorry

theorem pureIntExtGcd_bezout (a b : Int) :
    let (g, s, t) := pureIntExtGcd a b
    s * a + t * b = g := by
  sorry

end Hex

namespace HexArith

namespace Int

/--
Extended GCD on integers.

Trusted runtime contract: the `lean_hex_mpz_gcdext` attachment may replace this
pure Lean reference with a GMP-backed implementation that returns the same
`(g, s, t)` triple, where `g = Int.gcd a b` and `s * a + t * b = g`.
-/
@[extern "lean_hex_mpz_gcdext"]
def extGcd (a b : @& Int) : Nat × Int × Int :=
  Hex.pureIntExtGcd a b

theorem extGcd_fst (a b : Int) : (extGcd a b).1 = Int.gcd a b := by
  sorry

theorem extGcd_bezout (a b : Int) :
    let (g, s, t) := extGcd a b
    s * a + t * b = g := by
  sorry

end Int

namespace UInt64

/-- Public `UInt64` extended GCD API surface. -/
def extGcd (a b : UInt64) : UInt64 × Int × Int :=
  let (g, s, t) := Int.extGcd (Int.ofNat a.toNat) (Int.ofNat b.toNat)
  (.ofNat g, s, t)

theorem extGcd_fst (a b : UInt64) :
    (extGcd a b).1.toNat = Nat.gcd a.toNat b.toNat := by
  sorry

theorem extGcd_bezout (a b : UInt64) :
    let (g, s, t) := extGcd a b
    s * Int.ofNat a.toNat + t * Int.ofNat b.toNat = Int.ofNat g.toNat := by
  sorry

end UInt64

end HexArith
