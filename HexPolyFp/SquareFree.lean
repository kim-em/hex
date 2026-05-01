import HexModArith.Prime
import HexPolyFp.Basic

/-!
Executable square-free decomposition for `F_p[x]`.

This module implements a Yun-style square-free decomposition for
`Hex.FpPoly p`, recording the unit factor and the positive-multiplicity
square-free factors obtained from repeated gcd/derivative steps and
`p`-th-root descent in characteristic `p`. The public API carries an
explicit `Hex.Nat.Prime p` contract because the exported factorization and
square-free theorems are intended for prime-field coefficients.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- One square-free factor together with its multiplicity. -/
structure SquareFreeFactor (p : Nat) [ZMod64.Bounds p] where
  factor : FpPoly p
  multiplicity : Nat

/-- A square-free decomposition records the scalar unit and the nonconstant factors. -/
structure SquareFreeDecomposition (p : Nat) [ZMod64.Bounds p] where
  unit : ZMod64 p
  factors : List (SquareFreeFactor p)

/-- Detect the unit polynomial `1`. -/
private def isOne (f : FpPoly p) : Bool :=
  match f.degree? with
  | some 0 =>
      if f.coeff 0 = (1 : ZMod64 p) then
        true
      else
        false
  | _ => false

/-- Polynomial exponentiation uses square-and-multiply on the exponent bits. -/
private def pow (f : FpPoly p) (n : Nat) : FpPoly p :=
  let rec go (acc base : FpPoly p) (k : Nat) : FpPoly p :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then acc * base else acc
      go acc' (base * base) (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go 1 f n

/-- Multiply the factors in a square-free decomposition with their multiplicities. -/
def weightedProduct (factors : List (SquareFreeFactor p)) : FpPoly p :=
  factors.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) 1

private theorem weightedProduct_nil :
    weightedProduct ([] : List (SquareFreeFactor p)) = 1 := by
  rfl

private theorem weightedProduct_foldl_eq_mul
    (acc : FpPoly p) (factors : List (SquareFreeFactor p)) :
    factors.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) acc =
      acc * weightedProduct factors := by
  induction factors generalizing acc with
  | nil =>
      rw [weightedProduct_nil]
      exact (DensePoly.mul_one_right_poly acc).symm
  | cons sf factors ih =>
      unfold weightedProduct
      simp only [List.foldl_cons]
      rw [ih (acc * pow sf.factor sf.multiplicity)]
      rw [ih ((1 : FpPoly p) * pow sf.factor sf.multiplicity)]
      have hone :
          (1 : FpPoly p) * pow sf.factor sf.multiplicity =
            pow sf.factor sf.multiplicity := by
        exact one_mul (pow sf.factor sf.multiplicity)
      rw [hone]
      exact DensePoly.mul_assoc_poly acc (pow sf.factor sf.multiplicity) (weightedProduct factors)

private theorem weightedProduct_cons
    (sf : SquareFreeFactor p) (factors : List (SquareFreeFactor p)) :
    weightedProduct (sf :: factors) =
      pow sf.factor sf.multiplicity * weightedProduct factors := by
  unfold weightedProduct
  simp only [List.foldl_cons]
  rw [weightedProduct_foldl_eq_mul]
  exact congrArg (fun x => x * weightedProduct factors) (one_mul (pow sf.factor sf.multiplicity))

private theorem weightedProduct_append
    (left right : List (SquareFreeFactor p)) :
    weightedProduct (left ++ right) = weightedProduct left * weightedProduct right := by
  unfold weightedProduct
  rw [List.foldl_append]
  simpa [weightedProduct] using
    weightedProduct_foldl_eq_mul
      (p := p)
      (left.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) 1)
      right

private theorem weightedProduct_singleton (sf : SquareFreeFactor p) :
    weightedProduct [sf] = pow sf.factor sf.multiplicity := by
  rw [weightedProduct_cons, weightedProduct_nil]
  exact DensePoly.mul_one_right_poly (pow sf.factor sf.multiplicity)

private theorem weightedProduct_reverse_cons
    (sf : SquareFreeFactor p) (accRev : List (SquareFreeFactor p)) :
    weightedProduct (sf :: accRev).reverse =
      weightedProduct accRev.reverse * pow sf.factor sf.multiplicity := by
  rw [List.reverse_cons, weightedProduct_append, weightedProduct_singleton]

/--
Extract the formal `p`-th root by keeping exactly the coefficients whose
degrees are multiples of `p`.
-/
private def pthRoot (f : FpPoly p) : FpPoly p :=
  let rootSize := (f.size + p - 1) / p
  ofCoeffs <|
    (List.range rootSize).map (fun i => f.coeff (i * p)) |>.toArray

private theorem scale_one_poly (c : ZMod64 p) :
    DensePoly.scale c (1 : FpPoly p) = DensePoly.C c := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  change c * (DensePoly.C (1 : ZMod64 p)).coeff n = (DensePoly.C c).coeff n
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n => exact hzero

private theorem C_mul_eq_scale (c : ZMod64 p) (f : FpPoly p) :
    DensePoly.C c * f = DensePoly.scale c f := by
  have hscale := scale_mul_left c (1 : FpPoly p) f
  rw [one_mul, scale_one_poly] at hscale
  exact hscale.symm

private theorem scale_scale (c d : ZMod64 p) (f : FpPoly p) :
    DensePoly.scale c (DensePoly.scale d f) = DensePoly.scale (c * d) f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero_c : c * (0 : ZMod64 p) = 0 := by grind
  have hzero_d : d * (0 : ZMod64 p) = 0 := by grind
  have hzero_cd : (c * d) * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero_c]
  rw [DensePoly.coeff_scale _ _ _ hzero_d]
  rw [DensePoly.coeff_scale _ _ _ hzero_cd]
  grind

private theorem scale_one_left (f : FpPoly p) :
    DensePoly.scale (1 : ZMod64 p) f = f := by
  apply DensePoly.ext_coeff
  intro n
  have hzero : (1 : ZMod64 p) * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_scale _ _ _ hzero]
  grind

private theorem zmod64_coprime_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    Nat.Coprime a.toNat p := by
  rw [Nat.Coprime]
  have hnot_dvd : ¬ p ∣ a.toNat := by
    intro hdiv
    rcases hdiv with ⟨k, hk⟩
    have ha_pos : 0 < a.toNat := by
      by_cases hnat : a.toNat = 0
      · exfalso
        apply ha
        apply ZMod64.ext
        apply UInt64.toNat_inj.mp
        simpa [ZMod64.toNat_eq_val] using hnat
      · exact Nat.pos_of_ne_zero hnat
    have hk_pos : 0 < k := by
      cases k with
      | zero =>
          exfalso
          have : a.toNat = 0 := by simpa using hk
          omega
      | succ k => exact Nat.succ_pos k
    have hle : p ≤ a.toNat := by
      rw [hk]
      simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left p hk_pos
    exact (Nat.not_le_of_gt a.toNat_lt) hle
  have hgcd_dvd_p : Nat.gcd a.toNat p ∣ p := Nat.gcd_dvd_right a.toNat p
  rcases hp.2 (Nat.gcd a.toNat p) hgcd_dvd_p with hgcd | hgcd
  · exact hgcd
  · exfalso
    apply hnot_dvd
    rcases Nat.gcd_dvd_left a.toNat p with ⟨k, hk⟩
    rw [hgcd] at hk
    exact ⟨k, hk⟩

private theorem zmod64_mul_inv_eq_one_of_prime_ne_zero
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have hcop := zmod64_coprime_of_prime_ne_zero hp ha
  have hinv : (a⁻¹ * a).toNat = (1 : ZMod64 p).toNat := by
    simpa [ZMod64.toNat_one] using ZMod64.inv_mul_eq_one (p := p) a hcop
  have hcomm : a * a⁻¹ = a⁻¹ * a := by grind
  rw [hcomm]
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  simpa [ZMod64.toNat_eq_val] using hinv

private theorem leadingCoeff_ne_zero_of_isZero_false
    (f : FpPoly p) (hzero : f.isZero = false) :
    DensePoly.leadingCoeff f ≠ 0 := by
  have hpos : 0 < f.size := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
      Nat.pos_iff_ne_zero] using hzero
  have hlast := DensePoly.coeff_last_ne_zero_of_pos_size f hpos
  have hlead : DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
    unfold DensePoly.leadingCoeff DensePoly.coeff
    rw [Array.back?_eq_getElem?]
    have hidx : f.coeffs.size - 1 < f.coeffs.size := by
      simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
    simp [Array.getD, DensePoly.size, hidx]
  rw [hlead]
  exact hlast

/-- Split off the leading coefficient so the recursive Yun loop can work on a monic input. -/
private def normalizeMonic (f : FpPoly p) : ZMod64 p × FpPoly p :=
  if f.isZero then
    (0, 0)
  else
    let unit := DensePoly.leadingCoeff f
    (unit, DensePoly.scale unit⁻¹ f)

private theorem normalizeMonic_zero
    (f : FpPoly p) (hzero : f.isZero = true) :
    normalizeMonic f = (0, 0) := by
  simp [normalizeMonic, hzero]

private theorem eq_zero_of_isZero_true
    (f : FpPoly p) (hzero : f.isZero = true) :
    f = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hsize : f.size = 0 := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hzero
  rw [DensePoly.coeff_eq_zero_of_size_le f (by omega)]
  exact DensePoly.coeff_zero n

private theorem normalizeMonic_zero_reconstruct
    (f : FpPoly p) (hzero : f.isZero = true) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  rw [normalizeMonic_zero f hzero]
  rw [eq_zero_of_isZero_true f hzero]
  exact mul_zero (DensePoly.C (0 : ZMod64 p))

private theorem normalizeMonic_nonzero
    (f : FpPoly p) (hzero : f.isZero = false) :
    normalizeMonic f =
      (DensePoly.leadingCoeff f, DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) := by
  simp [normalizeMonic, hzero]

private theorem normalizeMonic_nonzero_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  rw [normalizeMonic_nonzero f hzero]
  rw [C_mul_eq_scale, scale_scale]
  have hlead_ne := leadingCoeff_ne_zero_of_isZero_false f hzero
  rw [zmod64_mul_inv_eq_one_of_prime_ne_zero hp hlead_ne]
  exact scale_one_left f

private theorem normalizeMonic_reconstruct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f := by
  cases hzero : f.isZero
  · exact normalizeMonic_nonzero_reconstruct hp f hzero
  · exact normalizeMonic_zero_reconstruct f hzero

/--
Yun's inner loop: peel off the factors with multiplicities `i`, `i + 1`, ...
from the coprime/repeated split `(c, w)`, consing each discovered factor onto
the reverse-order accumulator.
-/
private def yunFactors
    (c w : FpPoly p) (i : Nat) (fuel : Nat)
    (accRev : List (SquareFreeFactor p)) :
    List (SquareFreeFactor p) × FpPoly p :=
  match fuel with
  | 0 => (accRev, w)
  | fuel + 1 =>
      if isOne c then
        (accRev, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let accRev' :=
          if isOne z then
            accRev
          else
            { factor := z, multiplicity := i } :: accRev
        yunFactors y (w / y) (i + 1) fuel accRev'

/--
Specification payload for `yunFactors`: the first component is the product
contributed by factors discovered from `(c, w, i, fuel)`, and the second is
the repeated part that remains for the `p`-th-root descent.
-/
private def yunFactorsContribution
    (c w : FpPoly p) (i : Nat) : Nat → FpPoly p × FpPoly p
  | 0 => (1, w)
  | fuel + 1 =>
      if isOne c then
        (1, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let tail := yunFactorsContribution y (w / y) (i + 1) fuel
        let contribution :=
          if isOne z then
            tail.1
          else
            pow z i * tail.1
        (contribution, tail.2)

private theorem yunFactors_reconstruction_invariant
    (c w : FpPoly p) (i fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    let loop := yunFactors c w i fuel accRev
    let contribution := yunFactorsContribution c w i fuel
    loop.2 = contribution.2 ∧
      weightedProduct loop.1.reverse =
        weightedProduct accRev.reverse * contribution.1 := by
  induction fuel generalizing c w i accRev with
  | zero =>
      simp [yunFactors, yunFactorsContribution]
  | succ fuel ih =>
      simp only [yunFactors, yunFactorsContribution]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := DensePoly.gcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (i + 1) accRev
        · have htail := ih y (w / y) (i + 1) ({ factor := z, multiplicity := i } :: accRev)
          constructor
          · simpa [y, z, hz] using htail.1
          · have hmul :
                weightedProduct (yunFactors y (w / y) (i + 1) fuel
                    ({ factor := z, multiplicity := i } :: accRev)).1.reverse =
                  weightedProduct accRev.reverse *
                    (pow z i * (yunFactorsContribution y (w / y) (i + 1) fuel).1) := by
              calc
                weightedProduct (yunFactors y (w / y) (i + 1) fuel
                    ({ factor := z, multiplicity := i } :: accRev)).1.reverse
                    = weightedProduct ({ factor := z, multiplicity := i } :: accRev).reverse *
                        (yunFactorsContribution y (w / y) (i + 1) fuel).1 := by
                          simpa [y, z] using htail.2
                _ = (weightedProduct accRev.reverse * pow z i) *
                        (yunFactorsContribution y (w / y) (i + 1) fuel).1 := by
                          rw [weightedProduct_reverse_cons]
                _ = weightedProduct accRev.reverse *
                        (pow z i * (yunFactorsContribution y (w / y) (i + 1) fuel).1) := by
                          exact DensePoly.mul_assoc_poly
                            (weightedProduct accRev.reverse) (pow z i)
                            (yunFactorsContribution y (w / y) (i + 1) fuel).1
            simpa [y, z, hz] using hmul

/--
Tail-recursive square-free decomposition over `F_p[x]`, accumulating factors
in reverse output order. A derivative-zero branch descends through the formal
`p`-th root and scales multiplicities by `p`.
-/
private def squareFreeAuxRev (f : FpPoly p) (multiplicity : Nat) :
    Nat → List (SquareFreeFactor p) → List (SquareFreeFactor p)
  | 0, accRev => accRev
  | fuel + 1, accRev =>
      if f.isZero then
        accRev
      else
        let df := DensePoly.derivative f
        if df.isZero then
          squareFreeAuxRev (pthRoot f) (multiplicity * p) fuel accRev
        else
          let g := DensePoly.gcd f df
          let c := f / g
          let loop := yunFactors c g multiplicity fuel accRev
          let accRev' := loop.1
          let repeated := loop.2
          if isOne repeated then
            accRev'
          else
            squareFreeAuxRev (pthRoot repeated) (multiplicity * p) fuel accRev'

/--
Recursive square-free decomposition over `F_p[x]`. A derivative-zero branch
descends through the formal `p`-th root and scales multiplicities by `p`.
-/
private def squareFreeAux (f : FpPoly p) (multiplicity : Nat)
    (fuel : Nat) : List (SquareFreeFactor p) :=
  (squareFreeAuxRev f multiplicity fuel []).reverse

private theorem squareFreeAuxRev_pairwise_coprime
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (squareFreeAuxRev f multiplicity fuel accRev).reverse.Pairwise
      (fun a b => DensePoly.gcd a.factor b.factor = 1) := by
  sorry

private theorem yunFactors_factors_squareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hacc :
      ∀ sf ∈ accRev.reverse, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1) :
    ∀ sf ∈
        (yunFactors (f / DensePoly.gcd f (DensePoly.derivative f))
          (DensePoly.gcd f (DensePoly.derivative f)) multiplicity fuel accRev).1.reverse,
      DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  sorry

private theorem squareFreeAuxRev_factors_squareFree
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hacc :
      ∀ sf ∈ accRev.reverse, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1) :
    ∀ sf ∈ (squareFreeAuxRev f multiplicity fuel accRev).reverse,
      DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simpa [squareFreeAuxRev] using hacc
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simpa [hzero] using hacc
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev hacc
        · simp [hdf]
          let g := DensePoly.gcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactors c g multiplicity fuel accRev
          have hloop :
              ∀ sf ∈ loop.1.reverse,
                DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
            simpa [loop, c, g] using
              yunFactors_factors_squareFree_of_derivative_split hp f multiplicity fuel
                accRev hdf hacc
          by_cases hrepeated : isOne loop.2
          · simpa [loop, c, g, hrepeated] using hloop
          · simpa [loop, c, g, hrepeated] using
              ih (pthRoot loop.2) (multiplicity * p) loop.1 hloop

/--
Compute a square-free decomposition by normalizing away the leading scalar and
running Yun's algorithm on the resulting monic polynomial.
-/
def squareFreeDecomposition (hp : Hex.Nat.Prime p) (f : FpPoly p) : SquareFreeDecomposition p :=
  let _ := hp
  let normalized := normalizeMonic f
  let unit := normalized.1
  let monicPart := normalized.2
  let factors := squareFreeAux monicPart 1 (monicPart.size + 1)
  { unit, factors }

theorem squareFree_pairwise_coprime (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    d.factors.Pairwise (fun a b => DensePoly.gcd a.factor b.factor = 1) := by
  unfold squareFreeDecomposition squareFreeAux
  exact squareFreeAuxRev_pairwise_coprime (normalizeMonic f).2 1 ((normalizeMonic f).2.size + 1) []

theorem squareFree_weightedProduct (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    DensePoly.C d.unit * weightedProduct d.factors = f := by
  sorry

theorem squareFree_factors_squareFree (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  unfold squareFreeDecomposition squareFreeAux
  apply squareFreeAuxRev_factors_squareFree hp
  intro sf hsf
  simp at hsf

end FpPoly
end Hex
