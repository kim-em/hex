import HexModArith.Instances

/-!
Prime-modulus theorem scaffolding for `HexModArith.ZMod64`.

This module states the remaining Phase 1 public theorem surface for the
`UInt64`-backed `ZMod64 p` carrier: inverse correctness for coprime
elements, the no-zero-divisors corollary for prime moduli, and the
Fermat-style exponentiation law expected by downstream modular
polynomial and bridge code.
-/

namespace HexModArith

namespace ZMod64

variable {p : Nat} [NeZero p]

/--
When `a` is coprime to the modulus, the executable inverse candidate is
the expected multiplicative inverse in `ZMod64 p`.
-/
theorem invCandidate_mul_eq_one (a : ZMod64 p) (hcop : Nat.Coprime a.toNat p) :
    invCandidate a * a = 1 := by
  sorry

/--
For coprime residues, the partial inverse returns a witness whose
product with the original element is `1`.
-/
theorem inv?_spec (a : ZMod64 p) (hcop : Nat.Coprime a.toNat p) :
    ∃ b, inv? a = some b ∧ b * a = 1 := by
  sorry

/--
Over a prime modulus, a zero product forces one factor to vanish.
-/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (hp : Nat.Prime p) {a b : ZMod64 p}
    (h : a * b = 0) :
    a = 0 ∨ b = 0 := by
  sorry

/--
Fermat's little theorem for the executable `ZMod64` power operation.
-/
theorem pow_prime_eq_self (hp : Nat.Prime p) (a : ZMod64 p) :
    a ^ p = a := by
  sorry

end ZMod64

end HexModArith
