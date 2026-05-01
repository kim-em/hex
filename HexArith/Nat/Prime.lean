import HexArith.Nat.ModArith

/-!
Mathlib-free combinatorial and prime-number lemmas for `HexArith`.

This module owns the local `Hex.Nat.choose` and `Hex.Nat.Prime` surfaces that the
computational core needs for binomial divisibility and Fermat-style congruence
statements, without importing Mathlib into the root arithmetic layer.
-/

namespace Hex

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

theorem two_le {p : Nat} (hp : Hex.Nat.Prime p) : 2 ≤ p := hp.1

private theorem coprime_of_not_dvd {p a : Nat} (hp : Hex.Nat.Prime p)
    (ha : ¬ p ∣ a) : Nat.Coprime p a := by
  rw [Nat.Coprime]
  have hgcd_dvd_p : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  rcases hp.2 (Nat.gcd p a) hgcd_dvd_p with hgcd | hgcd
  · exact hgcd
  · exfalso
    apply ha
    rw [← hgcd]
    exact Nat.gcd_dvd_right p a

theorem dvd_mul {p a b : Nat} (hp : Hex.Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases hb : p ∣ b
  · exact Or.inr hb
  · exact Or.inl ((coprime_of_not_dvd hp hb).dvd_of_dvd_mul_right h)

end Prime

private theorem not_dvd_of_pos_lt {p k : Nat} (hk : 0 < k) (hk' : k < p) :
    ¬ p ∣ k := by
  intro hpk
  rcases hpk with ⟨c, hc⟩
  have hc_pos : 0 < c := by
    cases c with
    | zero => omega
    | succ c => exact Nat.succ_pos c
  have : p ≤ k := by
    rw [hc]
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left p hc_pos
  omega

private theorem choose_one_right (n : Nat) : choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [choose]
      rw [ih]
      omega

private theorem choose_succ_mul_eq (n k : Nat) :
    (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [choose]
  | succ n ih =>
      cases k with
      | zero =>
          simp [choose, choose_one_right]
          omega
      | succ k =>
          grind [choose]

private theorem choose_prime_dvd_from_mul_identity {p k : Nat} (hp : Prime p)
    (hk : 0 < k) (hk' : k < p) : p ∣ choose p k := by
  cases k with
  | zero => omega
  | succ k =>
      cases p with
      | zero => omega
      | succ p =>
          have hmul : p + 1 ∣ (k + 1) * choose (p + 1) (k + 1) := by
            rw [choose_succ_mul_eq]
            exact Nat.dvd_mul_right (p + 1) (choose p k)
          rcases Prime.dvd_mul hp hmul with hdiv | hdiv
          · exact False.elim (not_dvd_of_pos_lt hk hk' hdiv)
          · exact hdiv

private def chooseTerm (n a b k : Nat) : Nat :=
  choose n k * a ^ (n - k) * b ^ k

private def chooseSum (n a b : Nat) : Nat -> Nat
  | 0 => 0
  | k + 1 => chooseSum n a b k + chooseTerm n a b k

private theorem choose_eq_zero_of_lt {n k : Nat} (h : n < k) : choose n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          simp [choose]
          by_cases hk : n < k
          · simp [ih hk]
            exact ih (by omega)
          · exfalso
            omega

private theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [choose, ih, choose_eq_zero_of_lt (by omega : n < n + 1)]

private theorem chooseSum_zero (a b : Nat) : chooseSum 0 a b 1 = 1 := by
  simp [chooseSum, chooseTerm]

private theorem chooseSum_succ_row (n a b m : Nat) (hm : m ≤ n + 1) :
    chooseSum (n + 1) a b (m + 1) =
      a * chooseSum n a b (m + 1) + b * chooseSum n a b m := by
  induction m with
  | zero =>
      simp [chooseSum, chooseTerm, Nat.pow_succ]
      rw [Nat.mul_comm]
  | succ m ih =>
      rw [chooseSum, ih (by omega)]
      unfold chooseTerm
      by_cases hlt : m < n
      · have hpow : a ^ (n - m) = a * a ^ (n - (m + 1)) := by
          have hsub' : n - m = n - (m + 1) + 1 := by omega
          rw [hsub', Nat.pow_succ, Nat.mul_comm]
        simp [chooseSum, chooseTerm, choose_succ_succ, hpow, Nat.pow_succ,
          Nat.mul_add, Nat.add_mul, Nat.add_assoc]
        ac_rfl
      · have hmn : m = n := by omega
        subst m
        have hzero : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
        simp [chooseSum, chooseTerm, choose_succ_succ, hzero, Nat.pow_succ,
          Nat.mul_add, Nat.add_assoc]
        ac_rfl

private theorem add_pow_chooseSum (n a b : Nat) :
    (a + b) ^ n = chooseSum n a b (n + 1) := by
  induction n with
  | zero =>
      simp [chooseSum, chooseTerm]
  | succ n ih =>
      calc
        (a + b) ^ (n + 1) = (a + b) ^ n * (a + b) := Nat.pow_succ (a + b) n
        _ = (a + b) ^ n * a + (a + b) ^ n * b := by rw [Nat.mul_add]
        _ = a * chooseSum n a b (n + 1) + b * chooseSum n a b (n + 1) := by
            rw [ih]
            ac_rfl
        _ = a * chooseSum n a b (n + 1 + 1) + b * chooseSum n a b (n + 1) := by
            have hzero : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
            have htail : chooseSum n a b (n + 1 + 1) = chooseSum n a b (n + 1) := by
              simp [chooseSum, chooseTerm, hzero]
            rw [htail]
        _ = chooseSum (n + 1) a b (n + 1 + 1) :=
            (chooseSum_succ_row n a b (n + 1) (by omega)).symm

private theorem add_pow_prime_mod_of_choose_dvd {p : Nat} (hp : Prime p) (a b : Nat)
    (hchoose : ∀ k, 0 < k → k < p → p ∣ choose p k) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p := by
  sorry

private theorem pow_prime_mod_from_add_pow {p : Nat} (hp : Prime p) (a : Nat)
    (hadd : ∀ a b, (a + b) ^ p % p = (a ^ p + b ^ p) % p) :
    a ^ p % p = a % p := by
  have hp_pos : 0 < p := by
    have htwo := hp.1
    omega
  induction a with
  | zero => simp [Nat.zero_pow hp_pos]
  | succ a ih =>
      have h := hadd a 1
      simp [Nat.one_pow] at h
      calc
        (a + 1) ^ p % p = (a ^ p + 1) % p := h
        _ = (a ^ p % p + 1) % p := (Nat.mod_add_mod (a ^ p) p 1).symm
        _ = (a % p + 1) % p := by rw [ih]
        _ = (a + 1) % p := Nat.mod_add_mod a p 1

/--
Every nontrivial binomial coefficient in the `p`th row of Pascal's triangle is
divisible by `p` when `p` is prime.
-/
theorem choose_prime_dvd {p k : Nat} (hp : Prime p) (hk : 0 < k) (hk' : k < p) :
    p ∣ choose p k := by
  exact choose_prime_dvd_from_mul_identity hp hk hk'

/--
Freshman's dream modulo a prime: all middle binomial terms vanish.
-/
theorem add_pow_prime_mod {p : Nat} (hp : Prime p) (a b : Nat) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p := by
  exact add_pow_prime_mod_of_choose_dvd hp a b (fun k hk hk' =>
    choose_prime_dvd hp hk hk')

/--
Fermat's little theorem in the form used by downstream modular arithmetic code.
-/
theorem pow_prime_mod {p : Nat} (hp : Prime p) (a : Nat) :
    a ^ p % p = a % p := by
  exact pow_prime_mod_from_add_pow hp a (fun a b => add_pow_prime_mod hp a b)

end Nat

end Hex
