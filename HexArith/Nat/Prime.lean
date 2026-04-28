import HexArith.Nat.ModArith

/-!
Mathlib-free combinatorial and prime-number scaffolding for `HexArith`.

This module owns the local `Nat.choose` and `Nat.Prime` surfaces that the
computational core needs for binomial divisibility and Fermat-style congruence
statements, without importing Mathlib into the root arithmetic layer.
-/

namespace Nat

/--
Binomial coefficients on natural numbers, defined by the Pascal recursion.
-/
def choose : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [choose]

@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := by
  rfl

@[simp] theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := by
  rfl

/--
A natural number is prime when it is at least `2` and its positive divisors are
trivial.
-/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

namespace Prime

theorem two_le {p : Nat} (hp : Nat.Prime p) : 2 ≤ p := hp.1

theorem dvd_mul {p a b : Nat} (hp : Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  sorry

end Prime

/--
Every nontrivial binomial coefficient in the `p`th row of Pascal's triangle is
divisible by `p` when `p` is prime.
-/
theorem choose_prime_dvd {p k : Nat} (hp : Nat.Prime p) (hk : 0 < k) (hk' : k < p) :
    p ∣ Nat.choose p k := by
  sorry

/--
Freshman's dream modulo a prime: all middle binomial terms vanish.
-/
theorem add_pow_prime_mod {p : Nat} (hp : Nat.Prime p) (a b : Nat) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p := by
  sorry

/--
Fermat's little theorem in the form used by downstream modular arithmetic code.
-/
theorem pow_prime_mod {p : Nat} (hp : Nat.Prime p) (a : Nat) :
    a ^ p % p = a % p := by
  sorry

end Nat
