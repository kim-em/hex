/-!
Binomial coefficients and prime-divisibility scaffolding.

This module provides the Phase 1 `Nat.choose` recursion together with
the binomial-divisibility, Fermat-style modular arithmetic, and
Euclid's lemma statements that the arithmetic library exposes.
-/

namespace Nat

/--
Predicate for prime natural numbers used by the arithmetic scaffold.
-/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/--
Standard recursive binomial coefficients.

This local definition supplies the Phase 1 `Nat.choose` API because the
project does not depend on Mathlib's combinatorics namespace.
-/
def choose : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_prime_dvd (hp : Nat.Prime p) (hk : 0 < k) (hk' : k < p) :
    p ∣ Nat.choose p k := by
  sorry

theorem add_pow_prime_mod (hp : Nat.Prime p) (a b : Nat) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p := by
  sorry

theorem pow_prime_mod (hp : Nat.Prime p) (a : Nat) :
    a ^ p % p = a % p := by
  sorry

namespace Prime

theorem dvd_mul (hp : Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  sorry

end Prime
end Nat
