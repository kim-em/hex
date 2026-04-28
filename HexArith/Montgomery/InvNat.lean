import HexArith.Montgomery.RedcNat

/-!
Montgomery inverse scaffolding for `HexArith`.

The runtime inverse is computed in wrapping `UInt64` arithmetic by Newton-style
doubling from the standard odd-modulus seed. The proof surface records the
expected modular-inverse properties for later phases.
-/

/-- One Newton/Hensel refinement step for the positive Montgomery inverse. -/
private def montPosInvStep (p x : UInt64) : UInt64 :=
  x * (2 - p * x)

/--
Starting from the odd-modulus seed `x = p`, six refinement steps lift the
inverse from mod `2^3` to mod `2^64`.
-/
def montPosInv (p : UInt64) : UInt64 :=
  let x1 := montPosInvStep p p
  let x2 := montPosInvStep p x1
  let x3 := montPosInvStep p x2
  let x4 := montPosInvStep p x3
  let x5 := montPosInvStep p x4
  montPosInvStep p x5

/-- The user-facing Montgomery inverse is the negated positive inverse. -/
def montInv (p : UInt64) : UInt64 :=
  0 - montPosInv p

/-- One Newton step doubles the number of correct bits in the inverse. -/
theorem newton_step (hp_odd : p % 2 = 1) (k : Nat)
    (hxk : p * x % 2 ^ k = 1) :
    p * (x * (2 - p * x)) % 2 ^ (2 * k) = 1 := by
  sorry

/-- The positive Montgomery inverse satisfies `p * x ≡ 1 (mod 2^64)`. -/
theorem montPosInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montPosInv p).toNat % UInt64.word = 1 := by
  sorry

/-- The negated Montgomery inverse satisfies `p * p' ≡ -1 (mod 2^64)`. -/
theorem montInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montInv p).toNat % UInt64.word = UInt64.word - 1 := by
  sorry
