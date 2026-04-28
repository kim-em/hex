import HexArith.Nat.ModArith
import HexArith.UInt64.Wide

/-!
Nat-level Barrett reduction for `HexArith`.

This module states the pure arithmetic reduction used by the `UInt64` Barrett
implementation. It works with the radix `R = 2^64` abstractly at `Nat`, leaving
all machine-word encoding details to later layers.
-/

/-- The single-word radix used by the `UInt64` Barrett reduction. -/
def barrettRadix : Nat := UInt64.word

/--
Barrett reduction at the Nat level.

Given `T = a * b` with `T < 2^64` and `pinv = floor(R / p)`, approximate the
quotient using one multiply-and-shift step and correct the remainder by at most
one subtraction.
-/
def barrettReduceNat (p pinv T : Nat) : Nat :=
  let q := T * pinv / barrettRadix
  let r := T - q * p
  if r ≥ p then r - p else r

/--
With `pinv = floor(R / p)` and `T < R`, Nat-level Barrett reduction returns the
same value as `% p`.
-/
theorem barrettReduceNat_eq_mod (hp : 1 < p) (hpinv : pinv = barrettRadix / p)
    (hT : T < barrettRadix) :
    barrettReduceNat p pinv T = T % p := by
  sorry

/-- Nat-level Barrett reduction always returns a canonical residue. -/
theorem barrettReduceNat_lt (hp : 1 < p) (hpinv : pinv = barrettRadix / p)
    (hT : T < barrettRadix) :
    barrettReduceNat p pinv T < p := by
  sorry
