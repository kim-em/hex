import HexArith.Nat.ModArith
import HexArith.UInt64.Wide

/-!
Nat-level Montgomery reduction for `HexArith`.

This file states the REDC computation purely over `Nat`, using the `UInt64`
word radix `R = 2^64`. The executable `UInt64` bridge in later modules is
proved against these definitions.
-/

/-- Nat-level Montgomery reduction with radix `R = 2^64`. -/
def redcNat (p p' T : Nat) : Nat :=
  let m := (T % UInt64.word) * p' % UInt64.word
  let u := (T + m * p) / UInt64.word
  if u < p then u else u - p

/--
Montgomery reduction computes a residue congruent to `T * R⁻¹` modulo `p`.
-/
theorem redcNat_eq_mod (hp_pos : 0 < p) (hp_lt : p < UInt64.word)
    (hpp' : p * p' % UInt64.word = UInt64.word - 1) (hT : T < p * UInt64.word) :
    redcNat p p' T * UInt64.word % p = T % p := by
  sorry

/-- Montgomery reduction lands in the canonical residue interval `[0, p)`. -/
theorem redcNat_lt (hp_pos : 0 < p) (hp_lt : p < UInt64.word)
    (hpp' : p * p' % UInt64.word = UInt64.word - 1) (hT : T < p * UInt64.word) :
    redcNat p p' T < p := by
  sorry

/--
The unreduced Montgomery quotient is always below `2p`, so one subtraction is
enough to normalize the result.
-/
theorem redcNat_u_lt_two_p (hp_pos : 0 < p) (hp_lt : p < UInt64.word)
    (hpp' : p * p' % UInt64.word = UInt64.word - 1) (hT : T < p * UInt64.word) :
    (T + ((T % UInt64.word) * p' % UInt64.word) * p) / UInt64.word < 2 * p := by
  sorry
