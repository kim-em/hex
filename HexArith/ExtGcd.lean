/-!
Extended GCD algorithms and specifications.

This module defines pure-`Nat`, `Int`, and `UInt64` extended-GCD
operations together with the core gcd and Bezout-certificate theorems
used by the arithmetic library.
-/

namespace HexArith

/--
Quotient/remainder pairing used by `extGcd`.

Lean 4.30's stdlib exposes `Nat.div` and `Nat.mod`, but not a public fused
`Nat.divMod`; keep the pairing local so the Euclidean step can switch to a
fused primitive once one is available.
-/
private def natDivMod (a b : Nat) : Nat × Nat :=
  (a / b, a % b)

/--
Compute the greatest common divisor of `a` and `b` together with
Bezout coefficients.
-/
def extGcd (a b : Nat) : Nat × Int × Int :=
  if hb : b = 0 then
    (a, 1, 0)
  else
    let _ := hb
    let qr := natDivMod a b
    let (g, s, t) := extGcd b qr.2
    (g, t, s - t * Int.ofNat qr.1)
termination_by b
decreasing_by
  simp_wf
  simpa [natDivMod] using (Nat.mod_lt a (Nat.pos_iff_ne_zero.2 hb))

private theorem int_ofNat_mod_add_div (a b : Nat) :
    ((a % b : Nat) : Int) + ((a / b : Nat) : Int) * (b : Int) = (a : Int) := by
  have h := Nat.mod_add_div a b
  rw [Nat.mul_comm] at h
  exact_mod_cast h

private theorem extGcd_bezout_step
    (a b q r : Nat) (s t g : Int)
    (hqr : ((r : Nat) : Int) + ((q : Nat) : Int) * (b : Int) = (a : Int))
    (hrec : s * (b : Int) + t * (r : Int) = g) :
    t * (a : Int) + (s - t * (q : Int)) * (b : Int) = g := by
  rw [← hqr]
  calc
    t * (((r : Nat) : Int) + ((q : Nat) : Int) * (b : Int)) +
        (s - t * (q : Int)) * (b : Int)
        = s * (b : Int) + t * (r : Int) := by
          simp only [Int.mul_add, Int.sub_mul, Int.mul_assoc]
          omega
    _ = g := hrec

theorem extGcd_fst (a b : Nat) : (extGcd a b).1 = Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
      rw [extGcd]
      by_cases hb : b = 0
      · simp [hb]
      · simp only [hb, ↓reduceDIte, natDivMod]
        have hrec :
            (extGcd b (a % b)).1 = Nat.gcd b (a % b) :=
          ih (a % b) (Nat.mod_lt a (Nat.pos_iff_ne_zero.2 hb)) b
        have hgcd : Nat.gcd b (a % b) = Nat.gcd a b := by
          rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm (a % b) b]
        exact hrec.trans hgcd

theorem extGcd_bezout (a b : Nat) :
    let (g, s, t) := extGcd a b
    s * a + t * b = g := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
      rw [extGcd]
      by_cases hb : b = 0
      · simp [hb]
      · simp only [hb, ↓reduceDIte, natDivMod]
        have hrec :
            let (g, s, t) := extGcd b (a % b)
            s * (b : Int) + t * ((a % b : Nat) : Int) = g :=
          ih (a % b) (Nat.mod_lt a (Nat.pos_iff_ne_zero.2 hb)) b
        rcases hstep : extGcd b (a % b) with ⟨g, s, t⟩
        simp [hstep] at hrec
        exact extGcd_bezout_step a b (a / b) (a % b) s t g
          (int_ofNat_mod_add_div a b) hrec

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
  let (g, s, t) := HexArith.Int.extGcd (Int.ofNat a.toNat) (Int.ofNat b.toNat)
  (UInt64.ofNat g, s, t)

theorem extGcd_fst (a b : UInt64) :
    (extGcd a b).1.toNat = Nat.gcd a.toNat b.toNat := by
  sorry

theorem extGcd_bezout (a b : UInt64) :
    let (g, s, t) := extGcd a b
    s * Int.ofNat a.toNat + t * Int.ofNat b.toNat = Int.ofNat g.toNat := by
  sorry

end UInt64

end HexArith
