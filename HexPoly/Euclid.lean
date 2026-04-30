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

/-- Law package for the executable dense-polynomial division operations.

The algorithms remain available for any coefficient type with the required operations, but
theorems that use long-division invariants should require this class rather than claiming
those invariants for arbitrary, potentially unlawful `Div` and `Sub` instances. -/
class DivModLaws (R : Type u) [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]
    [Div R] : Prop where
  divMod_remainder_degree_lt_of_pos_degree :
    ∀ p q : DensePoly R,
      0 < q.degree?.getD 0 → (divMod p q).2.degree?.getD 0 < q.degree?.getD 0
  divModMonic_eq_divMod_of_monic :
    ∀ (p q : DensePoly R) (hq : Monic q), divModMonic p q hq = divMod p q
  mod_mod_of_not_pos_degree :
    ∀ p q : DensePoly R, ¬ 0 < q.degree?.getD 0 → (p % q) % q = p % q

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

/-- Core division invariant: for positive-degree divisors, `divMod` returns a remainder whose
degree is strictly smaller than the divisor degree. -/
theorem divMod_remainder_degree_lt_of_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    0 < q.degree?.getD 0 → (divMod p q).2.degree?.getD 0 < q.degree?.getD 0 := by
  exact DivModLaws.divMod_remainder_degree_lt_of_pos_degree p q

/-- Monic division agrees with field-style division when the divisor is monic. This is the
implementation invariant relating the specialized `divModMonic` path to `divMod`. -/
theorem divModMonic_eq_divMod_of_monic [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) (hq : Monic q) :
    divModMonic p q hq = divMod p q := by
  exact DivModLaws.divModMonic_eq_divMod_of_monic p q hq

/-- A polynomial whose degree is already below the divisor is its own remainder. -/
theorem mod_eq_self_of_degree_lt [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    p.degree?.getD 0 < q.degree?.getD 0 → p % q = p := by
  intro hdeg
  have hdiv := divMod_eq_zero_self_of_degree_lt p q hdeg
  simpa [DensePoly.mod] using congrArg Prod.snd hdiv

/-- Constant-degree divisors are an idempotent edge case for `%`. -/
theorem mod_mod_of_not_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    ¬ 0 < q.degree?.getD 0 → (p % q) % q = p % q := by
  exact DivModLaws.mod_mod_of_not_pos_degree p q

/-- The computed remainder has degree below a positive-degree divisor. -/
theorem mod_degree_lt_of_pos_degree [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    0 < q.degree?.getD 0 → (p % q).degree?.getD 0 < q.degree?.getD 0 := by
  simpa [DensePoly.mod] using divMod_remainder_degree_lt_of_pos_degree p q

theorem div_mul_add_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    (p q : DensePoly R) :
    (p / q) * q + (p % q) = p := by
  simpa [DensePoly.div, DensePoly.mod] using divMod_spec p q

theorem modByMonic_eq_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) (hq : Monic q) :
    modByMonic p q hq = p % q := by
  rw [modByMonic_eq_divModMonic, mod_eq_divMod, divModMonic_eq_divMod_of_monic p q hq]

theorem mod_mod [One R] [Add R] [Sub R] [Mul R] [Div R]
    [DivModLaws R]
    (p q : DensePoly R) :
    (p % q) % q = p % q := by
  by_cases hq : 0 < q.degree?.getD 0
  · exact mod_eq_self_of_degree_lt (p % q) q (mod_degree_lt_of_pos_degree p q hq)
  · exact mod_mod_of_not_pos_degree p q hq

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

private theorem foldl_gcd_dvd_acc (xs : List Nat) (acc : Nat) :
    xs.foldl (fun g x => Nat.gcd g x) acc ∣ acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      exact Nat.dvd_trans (ih (Nat.gcd acc x)) (Nat.gcd_dvd_left acc x)

private theorem foldl_gcd_dvd_of_mem {xs : List Nat} {x acc : Nat}
    (hx : x ∈ xs) :
    xs.foldl (fun g x => Nat.gcd g x) acc ∣ x := by
  induction xs generalizing acc with
  | nil =>
      cases hx
  | cons y ys ih =>
      simp at hx
      cases hx with
      | inl hxy =>
          subst hxy
          exact Nat.dvd_trans (foldl_gcd_dvd_acc ys (Nat.gcd acc x))
            (Nat.gcd_dvd_right acc x)
      | inr hy =>
          exact ih (acc := Nat.gcd acc y) hy

private theorem contentNat_dvd_coeff (p : DensePoly Int) (n : Nat) :
    (contentNat p : Int) ∣ p.coeff n := by
  by_cases hn : n < p.size
  · rw [Int.ofNat_dvd_left]
    unfold contentNat coeff toArray
    have hmem : p.coeffs[n].natAbs ∈ p.coeffs.toList.map Int.natAbs := by
      apply List.mem_map.mpr
      refine ⟨p.coeffs[n], ?_, rfl⟩
      rw [List.mem_iff_getElem]
      exact ⟨n, by simpa [size] using hn, by simp [Array.getElem_toList]; rfl⟩
    have hfold := foldl_gcd_dvd_of_mem (acc := 0) hmem
    have hcoeff : (p.coeffs.getD n (Zero.zero : Int)).natAbs = p.coeffs[n].natAbs := by
      change (p.coeffs.getD n (0 : Int)).natAbs = p.coeffs[n].natAbs
      rw [Array.getElem_eq_getD (0 : Int)]
    rw [hcoeff]
    simpa only [List.foldl_map] using hfold
  · have hnle : p.size ≤ n := Nat.le_of_not_gt hn
    rw [coeff_eq_zero_of_size_le p hnle]
    exact ⟨0, by rw [Int.mul_zero]; rfl⟩

private theorem list_getD_map_ediv_zero (c : Int) (coeffs : List Int) (n : Nat) :
    (coeffs.map fun coeff => coeff / c).getD n (Zero.zero : Int) =
      coeffs.getD n (Zero.zero : Int) / c := by
  induction coeffs generalizing n with
  | nil =>
      exact (Int.zero_ediv c).symm
  | cons coeff coeffs ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simpa using ih n

theorem content_mul_primitivePart (p : DensePoly Int) :
    scale (content p) (primitivePart p) = p := by
  apply ext_coeff
  intro n
  calc
    (scale (content p) (primitivePart p)).coeff n =
        content p * (primitivePart p).coeff n := by
          exact coeff_scale (content p) (primitivePart p) n (Int.mul_zero _)
    _ = p.coeff n := by
      by_cases hc : contentNat p = 0
      · have hdiv := contentNat_dvd_coeff p n
        rw [hc] at hdiv
        rcases hdiv with ⟨k, hk⟩
        have hpzero : p.coeff n = 0 := by
          simpa using hk
        simp [content, primitivePart, hc, hpzero]
      · have hpart :
            (primitivePart p).coeff n = p.coeff n / content p := by
          unfold primitivePart content
          rw [if_neg hc]
          rw [coeff_ofCoeffs_list]
          rw [list_getD_map_ediv_zero]
          unfold coeff toArray Array.getD
          by_cases hn : n < p.coeffs.size
          · simp [hn]
          · simp [hn]
        have hmul : content p * (p.coeff n / content p) = p.coeff n := by
          unfold content
          exact Int.mul_ediv_cancel' (contentNat_dvd_coeff p n)
        rw [hpart, hmul]

/-- Construct a polynomial with prescribed residues modulo coprime factors. -/
def polyCRT {S : Type _} [Zero S] [DecidableEq S] [One S] [Add S] [Mul S]
    (a b u v s t : DensePoly S) : DensePoly S :=
  u * t * b + v * s * a

/-- `Congr p q m` means `p` and `q` differ by a multiple of `m`. -/
def Congr {S : Type _} [Zero S] [DecidableEq S] [Add S] [Sub S] [Mul S]
    (p q m : DensePoly S) : Prop :=
  m ∣ (p - q)

private theorem mod_sub_self_eq_mul_neg_div {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (p m : DensePoly S) :
    p % m - p = m * (0 - p / m) := by
  sorry

private theorem congr_mod_core {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (p m : DensePoly S) :
    m ∣ (p % m - p) := by
  exact ⟨0 - p / m, mod_sub_self_eq_mul_neg_div p m⟩

/-- Reduction modulo the modulus is congruent to the original polynomial over a lawful
coefficient ring. -/
theorem congr_mod {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    (p m : DensePoly S) :
    Congr (p % m) p m := by
  exact congr_mod_core p m

private theorem eq_add_mul_of_sub_eq_mul {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    {p q m r : DensePoly S} :
    p - q = m * r -> p = q + m * r := by
  intro hsub
  apply ext_coeff
  intro n
  have hcoeff := congrArg (fun x : DensePoly S => x.coeff n) hsub
  have hzero_sub : (0 : S) - (0 : S) = 0 := by grind
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  change (p - q).coeff n = (m * r).coeff n at hcoeff
  rw [coeff_sub p q n hzero_sub] at hcoeff
  rw [coeff_add q (m * r) n hzero_add]
  grind

private theorem add_zero_right {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    p + 0 = p := by
  apply ext_coeff
  intro n
  have hzero_add : (0 : S) + (0 : S) = 0 := by grind
  rw [coeff_add p 0 n hzero_add]
  simp
  grind

private theorem zero_mul_left {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (p : DensePoly S) :
    (0 : DensePoly S) * p = 0 := by
  change mul 0 p = 0
  have hzero : (0 : DensePoly S).coeffs = #[] := rfl
  simp [mul, isZero, hzero]

private theorem mod_self_eq_zero {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m : DensePoly S) :
    m % m = 0 := by
  sorry

private theorem zero_mod_eq_zero {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m : DensePoly S) :
    (0 : DensePoly S) % m = 0 := by
  sorry

private theorem mod_mul_self_left {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (m r : DensePoly S) :
    (m * r) % m = 0 := by
  rw [mod_mul_mod]
  rw [mod_self_eq_zero]
  rw [zero_mul_left]
  rw [zero_mod_eq_zero]

private theorem mod_add_mul_self {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    (q m r : DensePoly S) :
    (q + m * r) % m = q % m := by
  rw [mod_add_mod]
  rw [mod_mul_self_left]
  rw [add_zero_right]
  rw [mod_mod]

private theorem mod_eq_mod_of_dvd_sub {S : Type _}
    [Lean.Grind.CommRing S] [DecidableEq S] [Div S] [DivModLaws S]
    {p q m : DensePoly S} :
    m ∣ (p - q) -> p % m = q % m := by
  rintro ⟨r, hmul⟩
  rw [eq_add_mul_of_sub_eq_mul hmul]
  exact mod_add_mul_self q m r

/-- Congruent polynomials have the same canonical remainder once the divisor law package
supplies the executable `%` invariants. -/
theorem mod_eq_mod_of_congr {S : Type _} [Lean.Grind.CommRing S] [DecidableEq S] [Div S]
    [DivModLaws S]
    {p q m : DensePoly S} :
    Congr p q m -> p % m = q % m := by
  exact mod_eq_mod_of_dvd_sub

private theorem polyCRT_congr_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> s * a + t * b = 1 ->
    Congr (polyCRT a b u v s t) u a := by
  sorry

private theorem polyCRT_congr_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] ->
    (a b u v s t : DensePoly S) -> s * a + t * b = 1 ->
    Congr (polyCRT a b u v s t) v b := by
  sorry

/-- The CRT witness reduces to the prescribed first residue modulo `a` via monic reduction. -/
theorem polyCRT_modByMonic_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (ha : Monic a) -> s * a + t * b = 1 ->
    modByMonic (polyCRT a b u v s t) a ha = modByMonic u a ha := by
  intro S _ _ _ _ a b u v s t ha hbez
  rw [modByMonic_eq_mod]
  rw [modByMonic_eq_mod]
  exact mod_eq_mod_of_congr (polyCRT_congr_fst a b u v s t hbez)

/-- The CRT witness reduces to the prescribed first residue modulo `a`. -/
theorem polyCRT_mod_fst :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (ha : Monic a) -> s * a + t * b = 1 ->
    polyCRT a b u v s t % a = u % a := by
  intro S _ _ _ _ a b u v s t ha hbez
  simpa [modByMonic_eq_mod] using polyCRT_modByMonic_fst a b u v s t ha hbez

/-- The CRT witness reduces to the prescribed second residue modulo `b` via monic reduction. -/
theorem polyCRT_modByMonic_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (hb : Monic b) -> s * a + t * b = 1 ->
    modByMonic (polyCRT a b u v s t) b hb = modByMonic v b hb := by
  intro S _ _ _ _ a b u v s t hb hbez
  rw [modByMonic_eq_mod]
  rw [modByMonic_eq_mod]
  exact mod_eq_mod_of_congr (polyCRT_congr_snd a b u v s t hbez)

/-- The CRT witness reduces to the prescribed second residue modulo `b`. -/
theorem polyCRT_mod_snd :
    {S : Type _} -> [Lean.Grind.CommRing S] -> [DecidableEq S] -> [Div S] ->
    [DivModLaws S] ->
    (a b u v s t : DensePoly S) -> (hb : Monic b) -> s * a + t * b = 1 ->
    polyCRT a b u v s t % b = v % b := by
  intro S _ _ _ _ a b u v s t hb hbez
  simpa [modByMonic_eq_mod] using polyCRT_modByMonic_snd a b u v s t hb hbez

end DensePoly
end Hex
