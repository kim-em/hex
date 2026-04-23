import HexArith

/-!
Core `ZMod64` scaffolding.

This module introduces the `UInt64`-backed `ZMod64 (p : Nat)` carrier
for modular arithmetic modulo `p`, together with executable addition,
subtraction, multiplication, inversion, and exponentiation operations.
Small moduli route
multiplication through the shared Barrett-reduction scaffold from
`HexArith`; the theorem surface records the intended modular semantics
for later proof work.
-/

namespace HexModArith

/-- The machine-word radix underlying `UInt64`. -/
private def wordBase : Nat :=
  2 ^ 64

/-- `2^64` is positive. -/
private theorem wordBase_pos : 0 < wordBase := by
  decide

/-- `2^32` fits strictly below the `UInt64` radix. -/
private theorem twoPow32_lt_wordBase : 2 ^ 32 < wordBase := by
  decide

/--
`ZMod64 p` stores a canonical `UInt64` representative together with the
fact that its natural-number value lies below the modulus `p`.
-/
structure ZMod64 (p : Nat) where
  /-- The underlying machine-word representative. -/
  val : UInt64
  /-- The representative lies in the canonical range `[0, p)`. -/
  isLt : val.toNat < p

namespace ZMod64

/-- View a residue as a natural number. -/
def toNat (a : ZMod64 p) : Nat :=
  a.val.toNat

/-- Any inhabited `ZMod64 p` witnesses that the modulus is positive. -/
theorem p_pos (a : ZMod64 p) : 0 < p := by
  exact Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.succ_le_of_lt a.isLt)

/--
Construct a canonical residue from a natural number by reducing modulo
`p` and storing the resulting `UInt64` word.
-/
def ofNat (p n : Nat) (hp : 0 < p) : ZMod64 p := by
  refine ⟨UInt64.ofNat (n % p), ?_⟩
  rw [show (UInt64.ofNat (n % p)).toNat = (n % p) % wordBase by
    simpa using (UInt64.toNat_ofNat (n := n % p))]
  by_cases hpw : p < wordBase
  · have hmod : n % p < wordBase := Nat.lt_trans (Nat.mod_lt _ hp) hpw
    rw [Nat.mod_eq_of_lt hmod]
    exact Nat.mod_lt _ hp
  · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ wordBase_pos) (Nat.le_of_not_gt hpw)

/--
The zero residue for a positive modulus.
-/
def zero (p : Nat) (hp : 0 < p) : ZMod64 p :=
  ofNat p 0 hp

/--
The one residue for a positive modulus.
-/
def one (p : Nat) (hp : 0 < p) : ZMod64 p :=
  ofNat p 1 hp

/--
Executable modular addition on canonical representatives.
-/
def add (a b : ZMod64 p) : ZMod64 p :=
  ofNat p (a.toNat + b.toNat) a.p_pos

/--
Executable modular subtraction on canonical representatives.
-/
def sub (a b : ZMod64 p) : ZMod64 p :=
  ofNat p (a.toNat + p - b.toNat) a.p_pos

/-- Build the shared Barrett context for a small modulus. -/
private def barrettCtx (p : Nat) (hp1 : 1 < p) (hp32 : p < 2 ^ 32) :
    HexArith.BarrettCtx (UInt64.ofNat p) :=
  HexArith.BarrettCtx.mk (UInt64.ofNat p)
    (by
      rw [show (UInt64.ofNat p).toNat = p % wordBase by
        simpa using (UInt64.toNat_ofNat (n := p))]
      simpa [Nat.mod_eq_of_lt (Nat.lt_trans hp32 twoPow32_lt_wordBase)] using hp1)
    (by
      rw [show (UInt64.ofNat p).toNat = p % wordBase by
        simpa using (UInt64.toNat_ofNat (n := p))]
      simpa [Nat.mod_eq_of_lt (Nat.lt_trans hp32 twoPow32_lt_wordBase)] using hp32)

/--
Executable modular multiplication. Small moduli use the shared Barrett
context from `HexArith`; larger moduli fall back to direct Nat-level
reduction while preserving the canonical representative invariant.
-/
def mul (a b : ZMod64 p) : ZMod64 p :=
  let n :=
    if hp1 : 1 < p then
      if hp32 : p < 2 ^ 32 then
        let ctx := barrettCtx p hp1 hp32
        (ctx.mulMod a.val b.val).toNat
      else
        (a.toNat * b.toNat) % p
    else
      0
  ofNat p n a.p_pos

/--
Bezout-coefficient-based inverse candidate. When `a` is coprime to `p`,
the first coefficient returned by extended GCD is the intended inverse.
-/
def invCandidate (a : ZMod64 p) : ZMod64 p :=
  let (_, s, _) := HexArith.UInt64.extGcd a.val (.ofNat p)
  ofNat p (Int.toNat (s % Int.ofNat p)) a.p_pos

/--
Partial executable inverse. Non-units return `none`; units return the
extended-GCD inverse candidate reduced modulo `p`.
-/
def inv? (a : ZMod64 p) : Option (ZMod64 p) :=
  let (g, _, _) := HexArith.UInt64.extGcd a.val (.ofNat p)
  if g.toNat = 1 then
    some (invCandidate a)
  else
    none

/--
Executable modular exponentiation by squaring.
-/
def pow (a : ZMod64 p) (n : Nat) : ZMod64 p :=
  ofNat p (HexArith.powMod a.toNat n p) a.p_pos

/-- Canonical representatives stay in range after addition. -/
theorem add_toNat_lt (a b : ZMod64 p) :
    (add a b).toNat < p := by
  exact (add a b).isLt

/-- Canonical representatives stay in range after subtraction. -/
theorem sub_toNat_lt (a b : ZMod64 p) :
    (sub a b).toNat < p := by
  exact (sub a b).isLt

/-- Canonical representatives stay in range after multiplication. -/
theorem mul_toNat_lt (a b : ZMod64 p) :
    (mul a b).toNat < p := by
  exact (mul a b).isLt

/-- Canonical representatives stay in range after inversion. -/
theorem invCandidate_toNat_lt (a : ZMod64 p) :
    (invCandidate a).toNat < p := by
  exact (invCandidate a).isLt

/-- Canonical representatives stay in range after exponentiation. -/
theorem pow_toNat_lt (a : ZMod64 p) (n : Nat) :
    (pow a n).toNat < p := by
  exact (pow a n).isLt

/--
For moduli fitting in one word, `ofNat` stores the exact reduced
natural-number representative.
-/
theorem toNat_ofNat (hp : 0 < p) (hpw : p < wordBase) (n : Nat) :
    (ofNat p n hp).toNat = n % p := by
  sorry

/-- Addition computes the expected modular sum for one-word moduli. -/
theorem toNat_add (hpw : p < wordBase) (a b : ZMod64 p) :
    (add a b).toNat = (a.toNat + b.toNat) % p := by
  sorry

/-- Subtraction computes the expected modular difference for one-word moduli. -/
theorem toNat_sub (hpw : p < wordBase) (a b : ZMod64 p) :
    (sub a b).toNat = (a.toNat + p - b.toNat) % p := by
  sorry

/--
Small-modulus multiplication agrees with the intended product modulo `p`.
-/
theorem toNat_mul_of_small (hp1 : 1 < p) (hp32 : p < 2 ^ 32) (a b : ZMod64 p) :
    (mul a b).toNat = (a.toNat * b.toNat) % p := by
  sorry

/--
For one-word moduli, multiplication computes the intended modular
product.
-/
theorem toNat_mul (hpw : p < wordBase) (a b : ZMod64 p) :
    (mul a b).toNat = (a.toNat * b.toNat) % p := by
  sorry

/--
Exponentiation computes the expected modular power for one-word moduli.
-/
theorem toNat_pow (hpw : p < wordBase) (a : ZMod64 p) (n : Nat) :
    (pow a n).toNat = a.toNat ^ n % p := by
  sorry

/--
For units, the extended-GCD inverse candidate is a multiplicative
inverse modulo `p`.
-/
theorem toNat_mul_invCandidate (hpw : p < wordBase) (a : ZMod64 p)
    (hcop : Nat.Coprime a.toNat p) :
    (mul (invCandidate a) a).toNat = 1 % p := by
  sorry

/--
When `a` is coprime to `p`, the partial inverse returns the inverse
candidate.
-/
theorem inv?_eq_some (a : ZMod64 p) (hcop : Nat.Coprime a.toNat p) :
    inv? a = some (invCandidate a) := by
  sorry

end ZMod64
end HexModArith
