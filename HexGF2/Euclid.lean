import HexGF2.Multiply

/-!
Executable Euclidean-algorithm operations for packed `GF2Poly`.

This module adds long division with remainder to the packed `GF(2)` polynomial
representation, then derives gcd and extended-gcd routines from that division
surface. The computational updates exploit characteristic two, so subtraction is
implemented by the same XOR operation as addition.
-/
namespace Hex
namespace GF2Poly

/-- Tail-recursive long division for packed `GF(2)` polynomials. -/
private def divModAux (q : GF2Poly) (fuel : Nat) (quot rem : GF2Poly) :
    GF2Poly × GF2Poly :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      if q.isZero then
        (0, rem)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let term := monomial k
              divModAux q fuel (quot + term) (rem + q.mulXk k)
        | _, _ => (quot, rem)

/-- Polynomial long division over `GF(2)`. Division by `0` returns `(0, p)`. -/
def divMod (p q : GF2Poly) : GF2Poly × GF2Poly :=
  divModAux q (p.degree + 1) 0 p

/-- Quotient from polynomial long division over `GF(2)`. -/
def div (p q : GF2Poly) : GF2Poly :=
  (divMod p q).1

/-- Remainder from polynomial long division over `GF(2)`. -/
def mod (p q : GF2Poly) : GF2Poly :=
  (divMod p q).2

instance : Div GF2Poly where
  div := div

instance : Mod GF2Poly where
  mod := mod

/-- Divisibility in `GF(2)[x]` is witnessed by an explicit quotient. -/
instance : Dvd GF2Poly where
  dvd p q := ∃ r : GF2Poly, q = p * r

private theorem add_cancel_middle (a b c : GF2Poly) :
    (a + b) + (c + b) = a + c := by
  apply ext_coeff
  intro n
  rw [coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne]
  cases a.coeff n <;> cases b.coeff n <;> cases c.coeff n <;> rfl

private theorem add_pair_swap (a b c d : GF2Poly) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  apply ext_coeff
  intro n
  rw [coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne, coeff_add_eq_bne,
    coeff_add_eq_bne, coeff_add_eq_bne]
  cases a.coeff n <;> cases b.coeff n <;> cases c.coeff n <;>
    cases d.coeff n <;> rfl

/-- A single long-division update preserves quotient/remainder
reconstruction. -/
theorem quotient_step_reconstruct (quot rem q : GF2Poly) (k : Nat) :
    let term := monomial k
    (quot + term) * q + (rem + q.mulXk k) = quot * q + rem := by
  dsimp
  rw [add_monomial_mul]
  exact add_cancel_middle (quot * q) (q.mulXk k) rem

private theorem divModAux_reconstruct
    (q : GF2Poly) (fuel : Nat) (quot rem : GF2Poly) :
    let qr := divModAux q fuel quot rem
    qr.1 * q + qr.2 = quot * q + rem := by
  induction fuel generalizing quot rem with
  | zero =>
      rfl
  | succ fuel ih =>
      simp only [divModAux]
      by_cases hqzero : q.isZero = true
      · simp [eq_zero_of_isZero hqzero]
      · have hqzeroFalse : q.isZero = false := by
          cases h : q.isZero <;> simp [h] at hqzero ⊢
        simp [hqzeroFalse]
        cases hrem : rem.degree? with
        | none =>
            simp
        | some rd =>
            cases hq : q.degree? with
            | none =>
                simp
            | some qd =>
                simp
                by_cases hlt : rd < qd
                · simp [hlt]
                · simp [hlt]
                  rw [ih]
                  exact quotient_step_reconstruct quot rem q (rd - qd)

private theorem isZero_eq_true_of_degree?_eq_none {p : GF2Poly}
    (h : p.degree? = none) :
    p.isZero = true := by
  by_cases hzero : p.isZero = true
  · exact hzero
  · have hfalse : p.isZero = false := by
      cases hp : p.isZero <;> simp [hp] at hzero ⊢
    obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hfalse
    rw [hd] at h
    contradiction

private theorem divModAux_remainder_degree_lt
    {q : GF2Poly} {qd : Nat} (hq : q.degree? = some qd)
    (fuel : Nat) (quot rem : GF2Poly)
    (hremFuel : rem.isZero = true ∨ rem.degree < fuel) :
    let qr := divModAux q fuel quot rem
    qr.2.isZero = true ∨ qr.2.degree < q.degree := by
  induction fuel generalizing quot rem with
  | zero =>
      simp only [divModAux]
      cases hremFuel with
      | inl hzero =>
          exact Or.inl hzero
      | inr hlt =>
          omega
  | succ fuel ih =>
      simp only [divModAux]
      have hqzeroFalse : q.isZero = false := isZero_false_of_degree?_eq_some hq
      simp [hqzeroFalse]
      cases hrem : rem.degree? with
      | none =>
          simpa using Or.inl (isZero_eq_true_of_degree?_eq_none hrem)
      | some rd =>
          rw [hq]
          by_cases hlt : rd < qd
          · simp [hlt]
            right
            rw [degree_eq_of_degree?_eq_some hrem, degree_eq_of_degree?_eq_some hq]
            exact hlt
          · simp [hlt]
            have hrdFuel : rd < fuel + 1 := by
              cases hremFuel with
              | inl hzero =>
                  have hnone := degree?_eq_none_of_isZero hzero
                  rw [hrem] at hnone
                  contradiction
              | inr hltFuel =>
                  simpa [degree_eq_of_degree?_eq_some hrem] using hltFuel
            have hstep :=
              division_step_degree_lt (rem := rem) (q := q) (rd := rd) (qd := qd)
                hrem hq hlt
            have hnextFuel :
                (rem + q.mulXk (rd - qd)).isZero = true ∨
                  (rem + q.mulXk (rd - qd)).degree < fuel := by
              cases hstep with
              | inl hzero =>
                  exact Or.inl hzero
              | inr hdegree =>
                  exact Or.inr (Nat.lt_of_lt_of_le hdegree (Nat.le_of_lt_succ hrdFuel))
            have hih :=
              ih (quot + monomial (rd - qd)) (rem + q.mulXk (rd - qd)) hnextFuel
            simpa using hih

/-- Result package for the packed extended Euclidean algorithm. -/
structure XGCDResult where
  gcd : GF2Poly
  left : GF2Poly
  right : GF2Poly

/-- Tail-recursive extended Euclidean algorithm over packed `GF(2)`
polynomials. -/
private def xgcdAux
    (r₀ s₀ t₀ r₁ s₁ t₁ : GF2Poly) (fuel : Nat) : XGCDResult :=
  match fuel with
  | 0 => { gcd := r₀, left := s₀, right := t₀ }
  | fuel + 1 =>
      if r₁.isZero then
        { gcd := r₀, left := s₀, right := t₀ }
      else
        let qr := divMod r₀ r₁
        let q := qr.1
        let r := qr.2
        xgcdAux r₁ s₁ t₁ r (s₀ + q * s₁) (t₀ + q * t₁) fuel

/-- Extended gcd for packed `GF(2)` polynomials, returning the gcd together
with Bezout coefficients. -/
def xgcd (p q : GF2Poly) : XGCDResult :=
  xgcdAux p 1 0 q 0 1 (p.degree + q.degree + 2)

/-- Polynomial gcd over packed `GF(2)`. -/
def gcd (p q : GF2Poly) : GF2Poly :=
  (xgcd p q).gcd

/-- The division output reconstructs the dividend. -/
theorem divMod_spec (p q : GF2Poly) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  unfold divMod
  simpa using divModAux_reconstruct q (p.degree + 1) 0 p

private theorem one_eq_monomial_zero : (1 : GF2Poly) = monomial 0 := by
  change one = monomial 0
  simp [one, monomial]

private theorem mulXk_zero (p : GF2Poly) :
    p.mulXk 0 = p := by
  apply ext_coeff
  intro n
  rw [coeff_mulXk, coeff_shiftLeft]
  simp [coeff]

private theorem one_mul (p : GF2Poly) :
    (1 : GF2Poly) * p = p := by
  rw [one_eq_monomial_zero, monomial_mul, mulXk_zero]

private theorem mul_one (p : GF2Poly) :
    p * (1 : GF2Poly) = p := by
  rw [one_eq_monomial_zero, mul_monomial, mulXk_zero]

private theorem xgcd_step_bezout
    (p q r₀ s₀ t₀ r₁ s₁ t₁ div rem : GF2Poly)
    (h₀ : s₀ * p + t₀ * q = r₀)
    (h₁ : s₁ * p + t₁ * q = r₁)
    (hdiv : div * r₁ + rem = r₀) :
    (s₀ + div * s₁) * p + (t₀ + div * t₁) * q = rem := by
  calc
    (s₀ + div * s₁) * p + (t₀ + div * t₁) * q
        = (s₀ * p + (div * s₁) * p) + (t₀ * q + (div * t₁) * q) := by
          rw [left_distrib, left_distrib]
    _ = (s₀ * p + div * (s₁ * p)) + (t₀ * q + div * (t₁ * q)) := by
          rw [mul_assoc, mul_assoc]
    _ = (s₀ * p + t₀ * q) + (div * (s₁ * p) + div * (t₁ * q)) := by
          exact add_pair_swap (s₀ * p) (div * (s₁ * p)) (t₀ * q) (div * (t₁ * q))
    _ = (s₀ * p + t₀ * q) + div * (s₁ * p + t₁ * q) := by
          rw [right_distrib]
    _ = r₀ + div * r₁ := by
          rw [h₀, h₁]
    _ = rem := by
          rw [← hdiv, add_comm (div * r₁) rem]
          simp

private theorem xgcdAux_bezout
    (p q r₀ s₀ t₀ r₁ s₁ t₁ : GF2Poly) (fuel : Nat)
    (h₀ : s₀ * p + t₀ * q = r₀)
    (h₁ : s₁ * p + t₁ * q = r₁) :
    let result := xgcdAux r₀ s₀ t₀ r₁ s₁ t₁ fuel
    result.left * p + result.right * q = result.gcd := by
  induction fuel generalizing r₀ s₀ t₀ r₁ s₁ t₁ with
  | zero =>
      simp [xgcdAux, h₀]
  | succ fuel ih =>
      simp only [xgcdAux]
      by_cases hzero : r₁.isZero = true
      · simp [hzero, h₀]
      · have hzeroFalse : r₁.isZero = false := by
          cases h : r₁.isZero <;> simp [h] at hzero ⊢
        simp [hzeroFalse]
        let qr := divMod r₀ r₁
        let div := qr.1
        let rem := qr.2
        have hdiv : div * r₁ + rem = r₀ := by
          simpa [qr, div, rem] using divMod_spec r₀ r₁
        exact ih r₁ s₁ t₁ rem (s₀ + div * s₁) (t₀ + div * t₁)
          h₁ (xgcd_step_bezout p q r₀ s₀ t₀ r₁ s₁ t₁ div rem h₀ h₁ hdiv)

/-- The computed remainder has smaller degree than a nonzero divisor. -/
theorem mod_degree_lt (p q : GF2Poly) :
    q ≠ 0 → (p % q).isZero = true ∨ (p % q).degree < q.degree := by
  intro hqne
  have hqzeroFalse : q.isZero = false := by
    cases hqzero : q.isZero
    · rfl
    · exfalso
      exact hqne (eq_zero_of_isZero hqzero)
  obtain ⟨qd, hqdeg⟩ := degree?_isSome_of_isZero_false hqzeroFalse
  change ((divMod p q).2).isZero = true ∨ (divMod p q).2.degree < q.degree
  unfold divMod
  apply divModAux_remainder_degree_lt (q := q) (qd := qd) hqdeg
  by_cases hpzero : p.isZero = true
  · exact Or.inl hpzero
  · exact Or.inr (Nat.lt_succ_self p.degree)

/-- The gcd divides the left input. -/
theorem gcd_dvd_left (p q : GF2Poly) :
    gcd p q ∣ p := by
  sorry

/-- The gcd divides the right input. -/
theorem gcd_dvd_right (p q : GF2Poly) :
    gcd p q ∣ q := by
  sorry

/-- Any common divisor divides the computed gcd. -/
theorem dvd_gcd (d p q : GF2Poly) :
    d ∣ p → d ∣ q → d ∣ gcd p q := by
  sorry

/-- The extended-gcd output satisfies the Bezout identity. -/
theorem xgcd_bezout (p q : GF2Poly) :
    let r := xgcd p q
    r.left * p + r.right * q = r.gcd := by
  unfold xgcd
  apply xgcdAux_bezout
  · rw [one_mul, zero_mul, add_zero]
  · rw [zero_mul, one_mul, zero_add]

end GF2Poly
end Hex
