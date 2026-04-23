/-!
Nat-level Montgomery REDC scaffolding.

This module provides the Phase 1 pure-`Nat` REDC API and its key
correctness statements for the arithmetic library.
-/

namespace HexArith

/-- The Montgomery radix `R = 2^64` used throughout the arithmetic library. -/
def montgomeryRadix : Nat :=
  2 ^ 64

/--
Montgomery REDC at the natural-number level.

Given a modulus `p`, a Montgomery inverse witness `p'`, and an input
`T < p * R`, compute the standard single-word REDC remainder candidate.
-/
def redcNat (p p' T : Nat) : Nat :=
  let m := (T % montgomeryRadix) * p' % montgomeryRadix
  let u := (T + m * p) / montgomeryRadix
  if u < p then u else u - p

theorem redcNat_eq_mod (hp_pos : 0 < p) (hp_lt : p < montgomeryRadix)
    (hpp' : p * p' % montgomeryRadix = montgomeryRadix - 1) (hT : T < p * montgomeryRadix) :
    redcNat p p' T * montgomeryRadix % p = T % p := by
  sorry

theorem redcNat_lt (hp_pos : 0 < p) (hp_lt : p < montgomeryRadix)
    (hpp' : p * p' % montgomeryRadix = montgomeryRadix - 1) (hT : T < p * montgomeryRadix) :
    redcNat p p' T < p := by
  sorry

theorem redcNat_u_lt_two_p (hp_pos : 0 < p) (hp_lt : p < montgomeryRadix)
    (hpp' : p * p' % montgomeryRadix = montgomeryRadix - 1) (hT : T < p * montgomeryRadix) :
    (T + ((T % montgomeryRadix) * p' % montgomeryRadix) * p) / montgomeryRadix < 2 * p := by
  sorry

end HexArith
