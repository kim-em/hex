/-!
Extended GCD scaffolding.

This module provides the Phase 1 pure-`Nat`, `Int`, and `UInt64`
extended-GCD APIs and their key correctness statements for the
arithmetic library.
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
Tail-recursive `UInt64` extended Euclidean loop.

The remainders stay in `UInt64`; only the Bezout coefficients live in `Int`.
-/
private def uint64ExtGcdLoop
    (old_r r : UInt64) (old_s s old_t t : Int) : UInt64 × Int × Int :=
  if h : r = 0 then
    let _ := h
    (old_r, old_s, old_t)
  else
    let q := old_r / r
    let qz := Int.ofNat q.toNat
    uint64ExtGcdLoop r (old_r % r) s (old_s - qz * s) t (old_t - qz * t)
termination_by r.toNat
decreasing_by
  simp_wf
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by
    intro hr
    apply h
    exact UInt64.toNat_inj.mp hr))

/--
Pure-Lean `UInt64` extended GCD reference implementation.

This stays entirely in native `UInt64` arithmetic for the Euclidean reduction,
while the Bezout coefficients are tracked in `Int`.
-/
def pureUInt64ExtGcd (a b : UInt64) : UInt64 × Int × Int :=
  uint64ExtGcdLoop a b 1 0 0 1

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

This is the pure-Lean reference definition returning a triple `(g, s, t)`
with `g = Int.gcd a b` and `s * a + t * b = g`.
-/
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
