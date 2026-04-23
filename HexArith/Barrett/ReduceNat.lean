/-!
Nat-level Barrett reduction scaffolding.

This module provides the Phase 1 pure-`Nat` Barrett reduction API and
its key correctness statements for the arithmetic library.
-/

namespace HexArith

/-- The Barrett radix `R = 2^64` used throughout the arithmetic library. -/
def barrettRadix : Nat :=
  2 ^ 64

/--
Barrett reduction at the natural-number level.

Given a modulus `p`, reciprocal `pinv = floor(R / p)`, and input `T`,
compute the standard one-subtraction Barrett remainder candidate.
-/
def barrettReduceNat (p pinv T : Nat) : Nat :=
  let q := T * pinv / barrettRadix
  let r := T - q * p
  if r ≥ p then r - p else r

theorem barrettReduceNat_eq_mod (hp : 1 < p) (hpinv : pinv = barrettRadix / p)
    (hT : T < barrettRadix) :
    barrettReduceNat p pinv T = T % p := by
  sorry

theorem barrettReduceNat_lt (hp : 1 < p) (hpinv : pinv = barrettRadix / p)
    (hT : T < barrettRadix) :
    barrettReduceNat p pinv T < p := by
  sorry

end HexArith
