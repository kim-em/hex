import Init.Grind.Ring.Basic
import HexPoly.Operations

/-!
Executable Euclidean-algorithm operations for dense array-backed polynomials.

This module extends `DensePoly` with a field-based long-division routine, the
derived gcd and extended-gcd algorithms, integer content/primitive-part helpers,
and the existential polynomial CRT construction used by downstream libraries.
-/
namespace Hex

universe u

namespace DensePoly

variable {R : Type u} [Zero R] [DecidableEq R]

/-- The leading coefficient, or `0` for the zero polynomial. -/
def leadingCoeff (p : DensePoly R) : R :=
  p.coeffs.back?.getD 0

/-- The constant polynomial `1`. -/
instance [One R] : One (DensePoly R) where
  one := C 1

/-- A polynomial is monic when its leading coefficient is `1`. -/
def Monic [One R] (p : DensePoly R) : Prop :=
  p.leadingCoeff = 1

private def arrayDegreeAux (coeffs : Array R) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      let i := fuel
      if coeffs.getD i (Zero.zero : R) = (Zero.zero : R) then
        arrayDegreeAux coeffs fuel
      else
        some i

private def arrayDegree? (coeffs : Array R) : Option Nat :=
  arrayDegreeAux coeffs coeffs.size

private def subtractScaledShift [Sub R] [Mul R]
    (rem q : Array R) (shift : Nat) (coeff : R) : Array R :=
  Id.run do
    let mut next := rem
    for j in [0:q.size] do
      let idx := shift + j
      next := next.set! idx (next.getD idx (Zero.zero : R) - coeff * q.getD j (Zero.zero : R))
    return next

private def divModArrayAux [Sub R] [Mul R]
    (q : Array R) (qDegree : Nat) (scaleLead : R → R)
    (fuel : Nat) (quot rem : Array R) : Array R × Array R :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      match arrayDegree? rem with
      | none => (quot, rem)
      | some rd =>
          if _hdeg : rd < qDegree then
            (quot, rem)
          else
            let shift := rd - qDegree
            let coeff := scaleLead (rem.getD rd (Zero.zero : R))
            let quot := quot.set! shift coeff
            let rem := subtractScaledShift rem q shift coeff
            divModArrayAux q qDegree scaleLead fuel quot rem

private def divModArray [Sub R] [Mul R]
    (p q : DensePoly R) (scaleLead : R → R) : DensePoly R × DensePoly R :=
  if q.isZero then
    (0, p)
  else
    let qDegree := q.size - 1
    let quotientSize := p.size - qDegree
    let quot := Array.replicate quotientSize (Zero.zero : R)
    let qr := divModArrayAux q.toArray qDegree scaleLead p.size quot p.toArray
    (ofCoeffs qr.1, ofCoeffs qr.2)

/-- Long division by a monic divisor over a commutative ring. -/
private def divModMonicAux [One R] [Add R] [Sub R] [Mul R]
    (q : DensePoly R) (fuel : Nat)
    (quot rem : DensePoly R) : DensePoly R × DensePoly R :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      if _hq : q.isZero then
        (0, rem)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if _hdeg : rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let coeff := rem.leadingCoeff
              let term := monomial k coeff
              divModMonicAux q fuel (quot + term) (rem - term * q)
        | _, _ => (quot, rem)

/-- Divide by a monic polynomial. The remainder has degree below the divisor whenever the fuel
is sufficient, which is the case for normalized dense polynomials. -/
def divModMonic [One R] [Add R] [Sub R] [Mul R]
    (p q : DensePoly R) (_hmonic : Monic q) :
    DensePoly R × DensePoly R :=
  divModArray p q id

/-- Field-based long division with remainder. Division by `0` returns `(0, p)`. -/
private def divModAux [One R] [Add R] [Sub R] [Mul R] [Div R]
    (q : DensePoly R) (fuel : Nat)
    (quot rem : DensePoly R) : DensePoly R × DensePoly R :=
  match fuel with
  | 0 => (quot, rem)
  | fuel + 1 =>
      if _hq : q.isZero then
        (0, rem)
      else
        match rem.degree?, q.degree? with
        | some rd, some qd =>
            if _hdeg : rd < qd then
              (quot, rem)
            else
              let k := rd - qd
              let coeff := rem.leadingCoeff / q.leadingCoeff
              let term := monomial k coeff
              divModAux q fuel (quot + term) (rem - term * q)
        | _, _ => (quot, rem)

/-- Polynomial division with remainder over a field. -/
def divMod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R × DensePoly R :=
  if p.degree?.getD 0 < q.degree?.getD 0 then
    (0, p)
  else
    divModArray p q (fun coeff => coeff / q.leadingCoeff)

/-- Quotient from polynomial long division over a field. -/
def div [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  (divMod p q).1

/-- Remainder from polynomial long division over a field. -/
def mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  (divMod p q).2

/-- Remainder from long division by a monic polynomial over a commutative ring. -/
def modByMonic [One R] [Add R] [Sub R] [Mul R]
    (p q : DensePoly R) (hmonic : Monic q) : DensePoly R :=
  (divModMonic p q hmonic).2

instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Div (DensePoly R) where
  div := div

instance [One R] [Add R] [Sub R] [Mul R] [Div R] : Mod (DensePoly R) where
  mod := mod

/-- Commutative-ring divisibility for dense polynomials. -/
instance [Add R] [Mul R] : Dvd (DensePoly R) where
  dvd p q := ∃ r : DensePoly R, q = p * r

/-- Result package for polynomial extended gcd. -/
structure XGCDResult (R : Type u) [Zero R] [DecidableEq R] where
  gcd : DensePoly R
  left : DensePoly R
  right : DensePoly R

/-- Tail-recursive extended Euclidean algorithm. -/
private def xgcdAux [One R] [Add R] [Sub R] [Mul R] [Div R]
    (r₀ s₀ t₀ r₁ s₁ t₁ : DensePoly R) (fuel : Nat) : XGCDResult R :=
  match fuel with
  | 0 => { gcd := r₀, left := s₀, right := t₀ }
  | fuel + 1 =>
      if _hr : r₁.isZero then
        { gcd := r₀, left := s₀, right := t₀ }
      else
        let qr := divMod r₀ r₁
        let q := qr.1
        let r := qr.2
        xgcdAux r₁ s₁ t₁ r (s₀ - q * s₁) (t₀ - q * t₁) fuel

/-- Extended gcd over a field, returning the gcd together with Bezout coefficients. -/
def xgcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : XGCDResult R :=
  xgcdAux p 1 0 q 0 1 (p.size + q.size + 1)

/-- Polynomial gcd over a field. -/
def gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) : DensePoly R :=
  (xgcd p q).gcd

theorem divMod_spec [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    let qr := divMod p q
    qr.1 * q + qr.2 = p := by
  sorry

theorem gcd_dvd_left [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    gcd p q ∣ p := by
  sorry

theorem gcd_dvd_right [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    gcd p q ∣ q := by
  sorry

theorem dvd_gcd [One R] [Add R] [Sub R] [Mul R] [Div R]
    (d p q : DensePoly R) :
    d ∣ p → d ∣ q → d ∣ gcd p q := by
  sorry

theorem xgcd_bezout [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    let r := xgcd p q
    r.left * p + r.right * q = r.gcd := by
  sorry

theorem modByMonic_eq_divModMonic [One R] [Add R] [Sub R] [Mul R]
    (p q : DensePoly R) (hq : Monic q) :
    modByMonic p q hq = (divModMonic p q hq).2 := by
  rfl

theorem mod_eq_divMod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    p % q = (divMod p q).2 := by
  rfl

theorem divMod_eq_zero_self_of_degree_lt [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    p.degree?.getD 0 < q.degree?.getD 0 → divMod p q = (0, p) := by
  intro hdeg
  simp [divMod, hdeg]

/-- The computed remainder has degree below a positive-degree divisor. -/
theorem mod_degree_lt_of_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    0 < q.degree?.getD 0 → (p % q).degree?.getD 0 < q.degree?.getD 0 := by
  sorry

theorem div_mul_add_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    (p / q) * q + (p % q) = p := by
  simpa [DensePoly.div, DensePoly.mod] using divMod_spec p q

theorem modByMonic_eq_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) (hq : Monic q) :
    modByMonic p q hq = p % q := by
  sorry

theorem mod_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    (p % q) % q = p % q := by
  sorry

/-- Reducing both summands before addition preserves the canonical remainder. -/
theorem mod_add_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q m : DensePoly R) :
    (p + q) % m = ((p % m) + (q % m)) % m := by
  sorry

/-- Reducing both factors before multiplication preserves the canonical remainder. -/
theorem mod_mul_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q m : DensePoly R) :
    (p * q) % m = ((p % m) * (q % m)) % m := by
  sorry

end DensePoly

namespace DensePoly

/-- The nonnegative gcd of the coefficients of an integer polynomial. -/
private def contentNat (p : DensePoly Int) : Nat :=
  p.toArray.toList.foldl (fun acc coeff => Nat.gcd acc coeff.natAbs) 0

/-- The integer content of a polynomial. This is always nonnegative. -/
def content (p : DensePoly Int) : Int :=
  Int.ofNat (contentNat p)

/-- The primitive part obtained by dividing every coefficient by the content. -/
def primitivePart (p : DensePoly Int) : DensePoly Int :=
  let cNat := contentNat p
  if cNat = 0 then
    0
  else
    let c := Int.ofNat cNat
    ofCoeffs <|
      p.toArray.toList.map (fun coeff => coeff / c) |>.toArray

theorem content_mul_primitivePart (p : DensePoly Int) :
    scale (content p) (primitivePart p) = p := by
  sorry

/-- Construct a polynomial with prescribed residues modulo coprime factors. -/
def polyCRT {S : Type _} [Zero S] [DecidableEq S] [One S] [Add S] [Mul S]
    (a b u v s t : DensePoly S) : DensePoly S :=
  u * t * b + v * s * a

/-- `Congr p q m` means `p` and `q` differ by a multiple of `m`. -/
def Congr {S : Type _} [Zero S] [DecidableEq S] [Add S] [Sub S] [Mul S]
    (p q m : DensePoly S) : Prop :=
  m ∣ (p - q)

/-- Reduction modulo the modulus is congruent to the original polynomial. -/
theorem congr_mod {S : Type _} [Zero S] [DecidableEq S] [One S] [Add S] [Sub S] [Mul S] [Div S]
    (p m : DensePoly S) :
    Congr (p % m) p m := by
  sorry

/-- Congruent polynomials have the same canonical remainder. -/
theorem mod_eq_mod_of_congr {S : Type _} [Zero S] [DecidableEq S] [One S] [Add S] [Sub S] [Mul S] [Div S]
    {p q m : DensePoly S} :
    Congr p q m -> p % m = q % m := by
  intro _h
  sorry

/-- The CRT witness reduces to the prescribed first residue modulo `a` via monic reduction. -/
theorem polyCRT_modByMonic_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> (ha : Monic a) -> s * a + t * b = 1 ->
    modByMonic (polyCRT a b u v s t) a ha = modByMonic u a ha := by
  sorry

/-- The CRT witness reduces to the prescribed first residue modulo `a`. -/
theorem polyCRT_mod_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    (a b u v s t : DensePoly S) -> (ha : Monic a) -> s * a + t * b = 1 ->
    polyCRT a b u v s t % a = u % a := by
  intro S _ _ _ a b u v s t ha hbez
  simpa [modByMonic_eq_mod] using polyCRT_modByMonic_fst a b u v s t ha hbez

/-- The CRT witness reduces to the prescribed second residue modulo `b` via monic reduction. -/
theorem polyCRT_modByMonic_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> (hb : Monic b) -> s * a + t * b = 1 ->
    modByMonic (polyCRT a b u v s t) b hb = modByMonic v b hb := by
  sorry

/-- The CRT witness reduces to the prescribed second residue modulo `b`. -/
theorem polyCRT_mod_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    (a b u v s t : DensePoly S) -> (hb : Monic b) -> s * a + t * b = 1 ->
    polyCRT a b u v s t % b = v % b := by
  intro S _ _ _ a b u v s t hb hbez
  simpa [modByMonic_eq_mod] using polyCRT_modByMonic_snd a b u v s t hb hbez

end DensePoly
end Hex
