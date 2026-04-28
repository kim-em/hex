import HexArith.Nat.Prime
import HexModArith.Ring

/-!
Prime-modulus theorem surface for `hex-mod-arith`.

This module packages the `ZMod64` consequences that only hold when the modulus
is prime, reusing the upstream `HexArith.Nat.Prime` lemmas rather than
re-proving prime arithmetic locally.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

private theorem eq_zero_of_dvd_modulus {a : ZMod64 p} (h : p ∣ a.toNat) : a = 0 := by
  apply ext
  apply UInt64.toNat_inj.mp
  have hzero : a.toNat = 0 := Nat.eq_zero_of_dvd_of_lt h a.toNat_lt
  simpa [ZMod64.toNat_eq_val] using hzero

/--
Prime-modulus residues have no zero divisors: if `a * b = 0`, then one of the
factors is already zero.
-/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (hp : Nat.Prime p) {a b : ZMod64 p}
    (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have hmod : (a.toNat * b.toNat) % p = 0 := by
    simpa using congrArg ZMod64.toNat h
  have hdvd : p ∣ a.toNat * b.toNat := by
    have hdecomp := Nat.mod_add_div (a.toNat * b.toNat) p
    rw [hmod, Nat.zero_add] at hdecomp
    exact ⟨(a.toNat * b.toNat) / p, hdecomp.symm⟩
  rcases Nat.Prime.dvd_mul hp hdvd with hA | hB
  · exact Or.inl (eq_zero_of_dvd_modulus hA)
  · exact Or.inr (eq_zero_of_dvd_modulus hB)

/--
Fermat's little theorem for `ZMod64`: raising a residue mod a prime `p` to the
`p`th power returns the original residue.
-/
theorem pow_prime (hp : Nat.Prime p) (a : ZMod64 p) : a ^ p = a := by
  apply ext
  apply UInt64.toNat_inj.mp
  have hpow : (a ^ p).toNat = a.toNat := by
    calc
      (a ^ p).toNat = a.toNat ^ p % p := toNat_pow a p
      _ = a.toNat % p := Nat.pow_prime_mod hp a.toNat
      _ = a.toNat := Nat.mod_eq_of_lt a.toNat_lt
  simpa [ZMod64.toNat_eq_val] using hpow

end ZMod64

end Hex
