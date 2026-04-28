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
  sorry

/-- The computed remainder has smaller degree than a nonzero divisor. -/
theorem mod_degree_lt (p q : GF2Poly) :
    q ≠ 0 → (p % q).isZero = true ∨ (p % q).degree < q.degree := by
  sorry

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
  sorry

end GF2Poly
end Hex
