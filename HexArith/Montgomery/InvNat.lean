import HexArith.Montgomery.RedcNat

/-!
Montgomery inverses for `HexArith`.

The runtime inverse is computed in wrapping `UInt64` arithmetic by Newton-style
doubling from the standard odd-modulus seed. The proof surface records the
resulting modular-inverse properties.
-/

/-- One Newton/Hensel refinement step for the positive Montgomery inverse. -/
private def montPosInvStep (p x : UInt64) : UInt64 :=
  x * (2 - p * x)

/-- The executable wrapping Newton step lifts a 3-bit inverse to 6 bits. -/
private theorem montPosInvStep_mod_3_to_6 (p x : UInt64)
    (hx : p * x % 8 = 1) :
    p * montPosInvStep p x % 64 = 1 := by
  unfold montPosInvStep
  bv_decide (config := { timeout := 30 })

/-- The executable wrapping Newton step lifts a 6-bit inverse to 12 bits. -/
private theorem montPosInvStep_mod_6_to_12 (p x : UInt64)
    (hx : p * x % 64 = 1) :
    p * montPosInvStep p x % 4096 = 1 := by
  unfold montPosInvStep
  bv_decide (config := { timeout := 30 })

private theorem two_pow_dvd_uint64_word {t : Nat} (ht : t ≤ 64) :
    2 ^ t ∣ UInt64.word := by
  refine ⟨2 ^ (64 - t), ?_⟩
  calc
    UInt64.word = 2 ^ 64 := rfl
    _ = 2 ^ (t + (64 - t)) := by rw [Nat.add_sub_of_le ht]
    _ = 2 ^ t * 2 ^ (64 - t) := by rw [Nat.pow_add]

private theorem mod_uint64_word_mod_two_pow (n t : Nat) (ht : t ≤ 64) :
    n % UInt64.word % 2 ^ t = n % 2 ^ t := by
  exact Nat.mod_mod_of_dvd n (two_pow_dvd_uint64_word ht)

/-- Multiplication wrap at `2^64` is invisible when reducing modulo fewer bits. -/
private theorem UInt64.toNat_mul_mod_two_pow (a b : UInt64) {t : Nat}
    (ht : t ≤ 64) :
    (a * b).toNat % 2 ^ t = (a.toNat * b.toNat) % 2 ^ t := by
  simpa [UInt64.toNat_mul] using
    mod_uint64_word_mod_two_pow (a.toNat * b.toNat) t ht

/-- Subtraction wrap at `2^64` is invisible when reducing modulo fewer bits. -/
private theorem UInt64.toNat_sub_mod_two_pow (a b : UInt64) {t : Nat}
    (ht : t ≤ 64) :
    (a - b).toNat % 2 ^ t =
      (2 ^ 64 - b.toNat + a.toNat) % 2 ^ t := by
  simpa [UInt64.toNat_sub] using
    mod_uint64_word_mod_two_pow (2 ^ 64 - b.toNat + a.toNat) t ht

/--
Starting from the odd-modulus seed `x = p`, five refinement steps lift the
inverse from mod `2^3` to mod `2^96 ≥ 2^64`.
-/
def montPosInv (p : UInt64) : UInt64 :=
  let x1 := montPosInvStep p p
  let x2 := montPosInvStep p x1
  let x3 := montPosInvStep p x2
  let x4 := montPosInvStep p x3
  montPosInvStep p x4

/-- The user-facing Montgomery inverse is the negated positive inverse. -/
def montInv (p : UInt64) : UInt64 :=
  0 - montPosInv p

/-- The positive Montgomery inverse satisfies `p * x ≡ 1 (mod 2^64)`. -/
theorem montPosInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montPosInv p).toNat % UInt64.word = 1 := by
  sorry

/-- The negated Montgomery inverse satisfies `p * p' ≡ -1 (mod 2^64)`. -/
theorem montInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montInv p).toNat % UInt64.word = UInt64.word - 1 := by
  sorry
