/-!
Small Nat-level modular-arithmetic lemmas used by `HexArith` proofs.

The later Barrett and Montgomery developments work almost entirely with
congruences and exact division by powers of two. Lean core already exposes the
basic arithmetic operations; this file collects the missing bridge lemmas in one
place so downstream modules can import a compact interface.
-/
namespace Nat

/-- Exact divisibility lets us rewrite `n / d * d` back to `n`. -/
theorem div_mul_of_dvd {n d : Nat} (hd : d ∣ n) : (n / d) * d = n := by
  exact Nat.div_mul_cancel hd

/-- `n` decomposes into its quotient and remainder with respect to `d`. -/
theorem mod_add_div_eq (n d : Nat) : n % d + (n / d) * d = n := by
  simpa [Nat.mul_comm] using Nat.mod_add_div n d

/--
An odd number is coprime to every power of two; this is the shape needed for
Montgomery inversion over `R = 2^k`.
-/
theorem coprime_pow_two_of_odd {p k : Nat} (hp : p % 2 = 1) :
    Nat.Coprime p (2 ^ k) := by
  have hbase : Nat.Coprime p 2 := by
    rw [Nat.Coprime, Nat.gcd_comm p 2, Nat.gcd_rec 2 p, hp]
    rfl
  exact hbase.pow_right k

/-- The converse packaging of `coprime_pow_two_of_odd` for a fixed power of two. -/
theorem coprime_twoPow_right {p k : Nat} (hp : p % 2 = 1) :
    Nat.Coprime (2 ^ k) p := by
  simpa [Nat.coprime_comm] using coprime_pow_two_of_odd (p := p) (k := k) hp

/--
If `p * p' ≡ -1 (mod 2^k)`, then `p * p' + 1` is divisible by `2^k`.
This is the divisibility transfer form used when proving Montgomery exactness.
-/
theorem twoPow_dvd_mul_add_one_of_mod_eq_pred {p p' k : Nat}
    (h : (p * p') % (2 ^ k) = 2 ^ k - 1) :
    2 ^ k ∣ p * p' + 1 := by
  exact (Nat.mod_eq_sub_iff (a := p * p') (b := 2 ^ k) (c := 1)
    (by decide) (Nat.succ_le_of_lt (Nat.two_pow_pos k))).1 h

end Nat
