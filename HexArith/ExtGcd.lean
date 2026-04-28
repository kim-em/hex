/-!
Extended GCD APIs and correctness statements for the arithmetic
library.
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

This runs the Euclidean algorithm directly on `Int`, carrying Bezout
coefficients through the usual quotient/remainder updates.
-/
private def pureIntExtGcd.go (old_r r old_s s old_t t : Int) : Nat × Int × Int :=
  match r with
  | 0 => (old_r.natAbs, old_s, old_t)
  | .ofNat (n + 1) =>
      let q := old_r / Int.ofNat (n + 1)
      pureIntExtGcd.go (Int.ofNat (n + 1)) (old_r % Int.ofNat (n + 1))
        s (old_s - q * s) t (old_t - q * t)
  | .negSucc n =>
      let r := Int.negSucc n
      let q := old_r / r
      pureIntExtGcd.go r (old_r % r) s (old_s - q * s) t (old_t - q * t)
termination_by r.natAbs
decreasing_by
  · have hmod_nonneg : 0 ≤ old_r % Int.ofNat (n + 1) := by
      exact Int.emod_nonneg _ (Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero _))
    have hpos : (0 : Int) < Int.ofNat (n + 1) := by
      exact Int.ofNat_lt.mpr (Nat.succ_pos _)
    have hmod_lt : old_r % Int.ofNat (n + 1) < Int.ofNat (n + 1) := by
      exact Int.emod_lt_of_pos _ hpos
    have hnatAbs_lt :
        ((old_r % Int.ofNat (n + 1)).natAbs : Int) < (Int.ofNat (n + 1)).natAbs := by
      rw [Int.ofNat_natAbs_of_nonneg hmod_nonneg]
      simpa using hmod_lt
    exact Int.ofNat_lt.mp hnatAbs_lt
  · have hmod_nonneg : 0 ≤ old_r % Int.negSucc n := by
      exact Int.emod_nonneg _ (by simp)
    have hpos : (0 : Int) < Int.ofNat (n + 1) := by
      exact Int.ofNat_lt.mpr (Nat.succ_pos _)
    have hmod_lt : old_r % Int.negSucc n < Int.ofNat (n + 1) := by
      simpa [Int.negSucc_eq, Int.emod_neg] using (Int.emod_lt_of_pos old_r hpos)
    have hnatAbs_lt :
        ((old_r % Int.negSucc n).natAbs : Int) < (Int.negSucc n).natAbs := by
      rw [Int.ofNat_natAbs_of_nonneg hmod_nonneg, Int.natAbs_negSucc]
      exact hmod_lt
    exact Int.ofNat_lt.mp hnatAbs_lt

def pureIntExtGcd (a b : Int) : Nat × Int × Int :=
  pureIntExtGcd.go a b 1 0 0 1

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
