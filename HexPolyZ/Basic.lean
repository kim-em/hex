import HexPoly

/-!
Core `ZPoly` definitions for `hex-poly-z`.

This module specializes the generic dense-polynomial library to integer
coefficients, adds the shared congruence predicate used by Hensel lifting,
and exposes the content/primitive-part operations expected from the
`hex-poly-z` root library.
-/
namespace Hex

/-- Integer polynomials represented by the dense normalized coefficient type
from `HexPoly`. -/
abbrev ZPoly := DensePoly Int

namespace ZPoly

/-- Coefficientwise congruence modulo `m`. -/
def congr (f g : ZPoly) (m : Nat) : Prop :=
  ∀ i, (f.coeff i - g.coeff i) % (m : Int) = 0

/-- Two integer polynomials are coprime mod `p` when they admit a Bezout
combination congruent to `1` modulo `p`. -/
def coprimeModP (f g : ZPoly) (p : Nat) : Prop :=
  ∃ s t : ZPoly, congr (s * f + t * g) 1 p

/-- The nonnegative gcd of the coefficients of `f`. -/
def content (f : ZPoly) : Int :=
  DensePoly.content f

/-- Divide every coefficient by the content to obtain a primitive polynomial. -/
def primitivePart (f : ZPoly) : ZPoly :=
  DensePoly.primitivePart f

/-- A `ZPoly` is primitive when its content is `1`. -/
def Primitive (f : ZPoly) : Prop :=
  content f = 1

/-- View an integer polynomial as a rational polynomial. -/
def toRatPoly (f : ZPoly) : DensePoly Rat :=
  DensePoly.ofCoeffs <| f.toArray.map fun coeff : Int => (coeff : Rat)

theorem coeff_toRatPoly (f : ZPoly) (n : Nat) :
    (toRatPoly f).coeff n = (f.coeff n : Rat) := by
  unfold toRatPoly
  rw [DensePoly.coeff_ofCoeffs]
  unfold DensePoly.coeff DensePoly.toArray
  by_cases hn : n < f.coeffs.size
  · simp [Array.getD, hn]
  · simp [Array.getD, hn]
    change (0 : Rat) = ((0 : Int) : Rat)
    simp

theorem toRatPoly_zero :
    toRatPoly (0 : ZPoly) = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly]
  change ((0 : ZPoly).coeff n : Rat) = (0 : DensePoly Rat).coeff n
  rw [DensePoly.coeff_eq_zero_of_size_le (0 : ZPoly) (by simp)]
  exact (DensePoly.coeff_eq_zero_of_size_le (0 : DensePoly Rat) (by simp)).symm

theorem toRatPoly_C (c : Int) :
    toRatPoly (DensePoly.C c) = DensePoly.C (c : Rat) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly]
  rw [DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    change ((0 : Int) : Rat) = 0
    simp

theorem toRatPoly_one :
    toRatPoly (1 : ZPoly) = 1 := by
  exact toRatPoly_C 1

theorem toRatPoly_scale_int (c : Int) (f : ZPoly) :
    toRatPoly (DensePoly.scale c f) = DensePoly.scale (c : Rat) (toRatPoly f) := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly]
  rw [DensePoly.coeff_scale (R := Int) c f n (Int.mul_zero c)]
  rw [DensePoly.coeff_scale (R := Rat) (c : Rat) (toRatPoly f) n (by
    exact Rat.mul_zero (c : Rat))]
  rw [coeff_toRatPoly]
  simp

private theorem size_toRatPoly (f : ZPoly) :
    (toRatPoly f).size = f.size := by
  apply Nat.le_antisymm
  · by_cases hle : (toRatPoly f).size ≤ f.size
    · exact hle
    · have hlt : f.size < (toRatPoly f).size := Nat.lt_of_not_ge hle
      let i := (toRatPoly f).size - 1
      have hrat_ne : (toRatPoly f).coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (toRatPoly f) (by omega)
      have hf_zero : f.coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le f (by
          unfold i
          omega)
      exfalso
      apply hrat_ne
      rw [coeff_toRatPoly, hf_zero]
      rfl
  · by_cases hle : f.size ≤ (toRatPoly f).size
    · exact hle
    · have hlt : (toRatPoly f).size < f.size := Nat.lt_of_not_ge hle
      let i := f.size - 1
      have hf_ne : f.coeff i ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size f (by omega)
      have hrat_zero : (toRatPoly f).coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le (toRatPoly f) (by
          unfold i
          omega)
      exfalso
      apply hf_ne
      have hcast_zero : ((f.coeff i : Int) : Rat) = 0 := by
        rw [← coeff_toRatPoly f i]
        exact hrat_zero
      exact Rat.intCast_eq_zero_iff.mp hcast_zero

private theorem toRatPoly_mulCoeffStep (f g : ZPoly) (n i : Nat) (a : Int) (j : Nat) :
    DensePoly.mulCoeffStep (toRatPoly f) (toRatPoly g) n i (a : Rat) j =
      (DensePoly.mulCoeffStep (R := Int) f g n i a j : Rat) := by
  unfold DensePoly.mulCoeffStep
  by_cases hij : i + j = n
  · simp [hij, coeff_toRatPoly]
  · simp [hij]

private theorem toRatPoly_mulCoeffStep_fold (f g : ZPoly) (n i : Nat)
    (xs : List Nat) (a : Int) :
    xs.foldl (DensePoly.mulCoeffStep (toRatPoly f) (toRatPoly g) n i) (a : Rat) =
      ((xs.foldl (DensePoly.mulCoeffStep (R := Int) f g n i) a : Int) : Rat) := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [toRatPoly_mulCoeffStep]
      exact ih (DensePoly.mulCoeffStep (R := Int) f g n i a j)

private theorem toRatPoly_mulCoeffOuter_fold (f g : ZPoly) (n : Nat)
    (xs : List Nat) (a : Int) :
    xs.foldl
        (fun acc i =>
          (List.range (toRatPoly g).size).foldl
            (DensePoly.mulCoeffStep (toRatPoly f) (toRatPoly g) n i) acc)
        (a : Rat) =
      ((xs.foldl
        (fun acc i =>
          (List.range g.size).foldl (DensePoly.mulCoeffStep (R := Int) f g n i) acc)
        a : Int) : Rat) := by
  induction xs generalizing a with
  | nil =>
      rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [size_toRatPoly g]
      rw [toRatPoly_mulCoeffStep_fold]
      simpa [size_toRatPoly g] using
        ih ((List.range g.size).foldl (DensePoly.mulCoeffStep (R := Int) f g n i) a)

private theorem toRatPoly_mulCoeffSum (f g : ZPoly) (n : Nat) :
    DensePoly.mulCoeffSum (toRatPoly f) (toRatPoly g) n =
      (DensePoly.mulCoeffSum (R := Int) f g n : Rat) := by
  unfold DensePoly.mulCoeffSum
  rw [size_toRatPoly f]
  exact toRatPoly_mulCoeffOuter_fold f g n (List.range f.size) 0

theorem toRatPoly_mul (f g : ZPoly) :
    toRatPoly (f * g) = toRatPoly f * toRatPoly g := by
  apply DensePoly.ext_coeff
  intro n
  rw [coeff_toRatPoly, DensePoly.coeff_mul, DensePoly.coeff_mul]
  exact (toRatPoly_mulCoeffSum f g n).symm

private def ratCommonDen (coeffs : List Rat) : Nat :=
  coeffs.foldl (fun acc coeff => Nat.lcm acc coeff.den) 1

private def ratCoeffToIntWithDen (den : Nat) (coeff : Rat) : Int :=
  coeff.num * Int.ofNat (den / coeff.den)

private def normalizePrimitiveSign (f : ZPoly) : ZPoly :=
  if DensePoly.leadingCoeff f < 0 then
    DensePoly.scale (-1 : Int) f
  else
    f

private theorem ratCommonDen_foldl_preserves_dvd (coeffs : List Rat) {d acc : Nat}
    (hacc : d ∣ acc) :
    d ∣ coeffs.foldl (fun acc coeff => Nat.lcm acc coeff.den) acc := by
  induction coeffs generalizing acc with
  | nil =>
      exact hacc
  | cons coeff coeffs ih =>
      simp only [List.foldl_cons]
      exact ih (acc := Nat.lcm acc coeff.den)
        (Nat.dvd_trans hacc (Nat.dvd_lcm_left acc coeff.den))

private theorem ratCommonDen_foldl_dvd_of_mem (coeffs : List Rat) {q : Rat} {acc : Nat}
    (hq : q ∈ coeffs) :
    q.den ∣ coeffs.foldl (fun acc coeff => Nat.lcm acc coeff.den) acc := by
  induction coeffs generalizing acc with
  | nil =>
      cases hq
  | cons coeff coeffs ih =>
      simp only [List.foldl_cons]
      simp only [List.mem_cons] at hq
      cases hq with
      | inl hhead =>
          subst hhead
          exact ratCommonDen_foldl_preserves_dvd coeffs (Nat.dvd_lcm_right acc q.den)
      | inr htail =>
          exact ih (acc := Nat.lcm acc coeff.den) htail

private theorem ratCommonDen_dvd_of_mem (coeffs : List Rat) {q : Rat} (hq : q ∈ coeffs) :
    q.den ∣ ratCommonDen coeffs := by
  unfold ratCommonDen
  exact ratCommonDen_foldl_dvd_of_mem coeffs hq

private theorem ratCoeffToIntWithDen_cast (den : Nat) (coeff : Rat)
    (hden : coeff.den ∣ den) :
    ((ratCoeffToIntWithDen den coeff : Int) : Rat) = (den : Rat) * coeff := by
  sorry

/--
Clear denominators in a rational polynomial and return the primitive integer
representative of the resulting rational associate.
-/
def ratPolyPrimitivePart (f : DensePoly Rat) : ZPoly :=
  let den := ratCommonDen f.toArray.toList
  let scaled :=
    DensePoly.ofCoeffs <|
      f.toArray.toList.map (fun coeff => ratCoeffToIntWithDen den coeff) |>.toArray
  normalizePrimitiveSign (primitivePart scaled)

private theorem ratPolyPrimitivePart_rational_associate_core (f : DensePoly Rat) :
    ∃ unit : Rat, f = DensePoly.scale unit (toRatPoly (ratPolyPrimitivePart f)) := by
  sorry

/--
Executable primitive square-free decomposition data for integer-polynomial
normalization.

`primitive` is the content-free input. `squareFreeCore` is computed over
`Rat[x]` as `primitive / gcd(primitive, primitive')`, then converted back to a
primitive integer representative. `repeatedPart` records the same rational gcd,
also converted to a primitive integer representative. The proof layer relates
these representatives back to the primitive input up to a rational unit.
-/
structure PrimitiveSquareFreeDecomposition where
  primitive : ZPoly
  squareFreeCore : ZPoly
  repeatedPart : ZPoly

/-- Square-free over `Rat[x]`, expressed by the executable rational gcd. -/
def SquareFreeRat (f : ZPoly) : Prop :=
  DensePoly.gcd (toRatPoly f) (DensePoly.derivative (toRatPoly f)) = 1

/--
Compute the primitive square-free normalization data needed by the integer
factorization pipeline.
-/
def primitiveSquareFreeDecomposition (f : ZPoly) : PrimitiveSquareFreeDecomposition :=
  let primitive := primitivePart f
  if primitive.isZero then
    { primitive, squareFreeCore := 0, repeatedPart := 0 }
  else
    let ratPrimitive := toRatPoly primitive
    let derivative := DensePoly.derivative ratPrimitive
    if derivative.isZero then
      { primitive, squareFreeCore := primitive, repeatedPart := 1 }
    else
      let repeatedRat := DensePoly.gcd ratPrimitive derivative
      { primitive
        squareFreeCore := ratPolyPrimitivePart (ratPrimitive / repeatedRat)
        repeatedPart := ratPolyPrimitivePart repeatedRat }

/-- The square-free core projection of `primitiveSquareFreeDecomposition`. -/
def squareFreeCore (f : ZPoly) : ZPoly :=
  (primitiveSquareFreeDecomposition f).squareFreeCore

theorem congr_refl (f : ZPoly) (m : Nat) : congr f f m := by
  intro i
  simp

theorem congr_symm (f g : ZPoly) (m : Nat) (hfg : congr f g m) : congr g f m := by
  intro i
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero (hfg i) with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  grind

theorem congr_trans (f g h : ZPoly) (m : Nat) (hfg : congr f g m) (hgh : congr g h m) :
    congr f h m := by
  intro i
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero (hfg i) with ⟨c, hc⟩
  rcases Int.dvd_of_emod_eq_zero (hgh i) with ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  grind

theorem congr_add (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) :
    congr (f + g) (f' + g') m := by
  intro i
  rw [DensePoly.coeff_add (R := Int) (hzero := by rfl),
    DensePoly.coeff_add (R := Int) (hzero := by rfl)]
  apply Int.emod_eq_zero_of_dvd
  rcases Int.dvd_of_emod_eq_zero (hf i) with ⟨c, hc⟩
  rcases Int.dvd_of_emod_eq_zero (hg i) with ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  grind

private theorem dvd_mul_sub_mul_of_dvd_sub (m a b c d : Int)
    (hab : m ∣ a - b) (hcd : m ∣ c - d) :
    m ∣ a * c - b * d := by
  rcases hab with ⟨u, hu⟩
  rcases hcd with ⟨v, hv⟩
  refine ⟨u * c + b * v, ?_⟩
  grind

private theorem dvd_mulCoeffStep_sub (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) (n i j : Nat) (a b : Int)
    (hab : (m : Int) ∣ a - b) :
    (m : Int) ∣
      DensePoly.mulCoeffStep f g n i a j -
        DensePoly.mulCoeffStep f' g' n i b j := by
  unfold DensePoly.mulCoeffStep
  by_cases hij : i + j = n
  · simp [hij]
    have hprod : (m : Int) ∣ f.coeff i * g.coeff j - f'.coeff i * g'.coeff j :=
      dvd_mul_sub_mul_of_dvd_sub (m : Int) (f.coeff i) (f'.coeff i) (g.coeff j)
        (g'.coeff j) (Int.dvd_of_emod_eq_zero (hf i)) (Int.dvd_of_emod_eq_zero (hg j))
    rcases hab with ⟨u, hu⟩
    rcases hprod with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    grind
  · simp [hij]
    exact hab

private theorem dvd_mulCoeffStep_fold_sub (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) (n i : Nat) (xs : List Nat) (a b : Int)
    (hab : (m : Int) ∣ a - b) :
    (m : Int) ∣
      xs.foldl (DensePoly.mulCoeffStep f g n i) a -
        xs.foldl (DensePoly.mulCoeffStep f' g' n i) b := by
  induction xs generalizing a b with
  | nil =>
      simpa using hab
  | cons j xs ih =>
      simp only [List.foldl_cons]
      exact ih (DensePoly.mulCoeffStep f g n i a j)
        (DensePoly.mulCoeffStep f' g' n i b j)
        (dvd_mulCoeffStep_sub f g f' g' m hf hg n i j a b hab)

private theorem fold_mulCoeffStep_range_add_zero_tail (p q : ZPoly)
    (n i : Nat) (a : Int) (d : Nat) :
    (List.range (q.size + d)).foldl (DensePoly.mulCoeffStep p q n i) a =
      (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) a := by
  induction d with
  | zero =>
      rfl
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      have hcoeff : q.coeff (q.size + d) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le q (by omega)
      by_cases h : i + (q.size + d) = n
      · simp [h, hcoeff]
      · simp [h]

private theorem fold_mulCoeffStep_range_of_size_le (p q : ZPoly)
    (n i : Nat) (a : Int) {s : Nat} (hs : q.size ≤ s) :
    (List.range s).foldl (DensePoly.mulCoeffStep p q n i) a =
      (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) a := by
  have hs' : q.size + (s - q.size) = s := by omega
  rw [← hs']
  exact fold_mulCoeffStep_range_add_zero_tail p q n i a (s - q.size)

private theorem fold_mulCoeffStep_zero_left (p q : ZPoly) (n i : Nat) (a : Int)
    (hi : p.coeff i = 0) :
    (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) a = a := by
  induction q.size generalizing a with
  | zero =>
      rfl
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      unfold DensePoly.mulCoeffStep
      by_cases h : i + k = n
      · simp [h, hi]
      · simp [h]

private theorem fold_mulCoeffOuter_range_add_zero_tail (p q : ZPoly)
    (n d : Nat) :
    (List.range (p.size + d)).foldl
        (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0 =
      (List.range p.size).foldl
        (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0 := by
  induction d with
  | zero =>
      rfl
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hcoeff : p.coeff (p.size + d) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le p (by omega)
      exact fold_mulCoeffStep_zero_left p q n (p.size + d)
        ((List.range p.size).foldl
          (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0)
        hcoeff

private theorem mulCoeffSum_eq_outer_range_of_size_le (p q : ZPoly)
    (n : Nat) {s : Nat} (hs : p.size ≤ s) :
    (List.range s).foldl
        (fun acc i => (List.range q.size).foldl (DensePoly.mulCoeffStep p q n i) acc) 0 =
      DensePoly.mulCoeffSum p q n := by
  unfold DensePoly.mulCoeffSum
  have hs' : p.size + (s - p.size) = s := by omega
  rw [← hs']
  exact fold_mulCoeffOuter_range_add_zero_tail p q n (s - p.size)

private theorem dvd_mulCoeffOuter_fold_sub (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) (n innerBound : Nat)
    (hgb : g.size ≤ innerBound) (hg'b : g'.size ≤ innerBound)
    (xs : List Nat) (a b : Int) (hab : (m : Int) ∣ a - b) :
    (m : Int) ∣
      xs.foldl
          (fun acc i => (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) acc) a -
        xs.foldl
          (fun acc i => (List.range g'.size).foldl (DensePoly.mulCoeffStep f' g' n i) acc) b := by
  induction xs generalizing a b with
  | nil =>
      simpa using hab
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hnext : (m : Int) ∣
          (List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) a -
            (List.range g'.size).foldl (DensePoly.mulCoeffStep f' g' n i) b := by
        rw [← fold_mulCoeffStep_range_of_size_le f g n i a hgb,
          ← fold_mulCoeffStep_range_of_size_le f' g' n i b hg'b]
        exact dvd_mulCoeffStep_fold_sub f g f' g' m hf hg n i
          (List.range innerBound) a b hab
      exact ih
        ((List.range g.size).foldl (DensePoly.mulCoeffStep f g n i) a)
        ((List.range g'.size).foldl (DensePoly.mulCoeffStep f' g' n i) b)
        hnext

theorem congr_mul (f g f' g' : ZPoly) (m : Nat)
    (hf : congr f f' m) (hg : congr g g' m) :
    congr (f * g) (f' * g') m := by
  intro i
  rw [DensePoly.coeff_mul, DensePoly.coeff_mul]
  apply Int.emod_eq_zero_of_dvd
  let outerBound := max f.size f'.size
  let innerBound := max g.size g'.size
  rw [← mulCoeffSum_eq_outer_range_of_size_le f g i (s := outerBound) (by
    unfold outerBound
    exact Nat.le_max_left f.size f'.size)]
  rw [← mulCoeffSum_eq_outer_range_of_size_le f' g' i (s := outerBound) (by
    unfold outerBound
    exact Nat.le_max_right f.size f'.size)]
  exact dvd_mulCoeffOuter_fold_sub f g f' g' m hf hg i innerBound
    (by
      unfold innerBound
      exact Nat.le_max_left g.size g'.size)
    (by
      unfold innerBound
      exact Nat.le_max_right g.size g'.size)
    (List.range outerBound) 0 0 (by simp)

theorem content_mul_primitivePart (f : ZPoly) :
    DensePoly.scale (content f) (primitivePart f) = f := by
  simpa [content, primitivePart] using DensePoly.content_mul_primitivePart f

theorem primitivePart_primitive (f : ZPoly) (h : content f ≠ 0) :
    Primitive (primitivePart f) := by
  simpa [Primitive, content, primitivePart] using DensePoly.primitivePart_primitive f h

theorem primitiveSquareFreeDecomposition_primitive (f : ZPoly) :
    (primitiveSquareFreeDecomposition f).primitive = primitivePart f := by
  by_cases hzero : (primitivePart f).isZero = true
  · simp [primitiveSquareFreeDecomposition, hzero]
  · by_cases hderivative : (DensePoly.derivative (toRatPoly (primitivePart f))).isZero = true
    · simp [primitiveSquareFreeDecomposition, hzero, hderivative]
    · simp [primitiveSquareFreeDecomposition, hzero, hderivative]

private theorem normalizePrimitiveSign_zero :
    normalizePrimitiveSign (0 : ZPoly) = 0 := by
  unfold normalizePrimitiveSign
  split
  · exact DensePoly.scale_neg_one_zero
  · rfl

private theorem normalizePrimitiveSign_primitivePart_primitive (f : ZPoly)
    (h : content (normalizePrimitiveSign (primitivePart f)) ≠ 0) :
    Primitive (normalizePrimitiveSign (primitivePart f)) := by
  have hcontent_ne : content f ≠ 0 := by
    intro hcontent
    have hpart_zero : primitivePart f = 0 := by
      simpa [primitivePart] using
        DensePoly.primitivePart_eq_zero_of_content_eq_zero f (by simpa [content] using hcontent)
    apply h
    rw [hpart_zero, normalizePrimitiveSign_zero]
    simp [content, DensePoly.content_zero]
  by_cases hlead : DensePoly.leadingCoeff (primitivePart f) < 0
  · rw [normalizePrimitiveSign, if_pos hlead, Primitive, content,
      DensePoly.content_scale_neg_one]
    simpa [Primitive, content] using primitivePart_primitive f hcontent_ne
  · rw [normalizePrimitiveSign, if_neg hlead]
    exact primitivePart_primitive f hcontent_ne

theorem ratPolyPrimitivePart_primitive (f : DensePoly Rat)
    (h : content (ratPolyPrimitivePart f) ≠ 0) :
    Primitive (ratPolyPrimitivePart f) := by
  unfold ratPolyPrimitivePart at h ⊢
  exact normalizePrimitiveSign_primitivePart_primitive _ h

theorem ratPolyPrimitivePart_rational_associate (f : DensePoly Rat) :
    ∃ unit : Rat, f = DensePoly.scale unit (toRatPoly (ratPolyPrimitivePart f)) := by
  exact ratPolyPrimitivePart_rational_associate_core f

private theorem rat_scale_zero (p : DensePoly Rat) :
    DensePoly.scale 0 p = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) 0 p n (Rat.mul_zero 0)]
  rw [DensePoly.coeff_zero]
  exact Rat.zero_mul (p.coeff n)

private theorem rat_scale_one (p : DensePoly Rat) :
    DensePoly.scale 1 p = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Rat) 1 p n (Rat.mul_zero 1)]
  exact Rat.one_mul (p.coeff n)

private theorem densePoly_eq_zero_of_isZero_true {R : Type _} [Zero R] [DecidableEq R]
    (p : DensePoly R) (h : p.isZero = true) :
    p = 0 := by
  apply DensePoly.ext_coeff
  intro n
  have hsize : p.size = 0 := by
    simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using h
  rw [DensePoly.coeff_eq_zero_of_size_le p (by omega)]
  rw [DensePoly.coeff_zero]
  rfl

theorem primitiveSquareFreeDecomposition_reassembly_over_rat (f : ZPoly) :
    let d := primitiveSquareFreeDecomposition f
    ∃ unit : Rat,
      toRatPoly d.primitive =
        DensePoly.scale unit (toRatPoly d.squareFreeCore * toRatPoly d.repeatedPart) := by
  sorry

theorem primitiveSquareFreeDecomposition_squareFreeCore
    (f : ZPoly)
    (hcore : (primitiveSquareFreeDecomposition f).squareFreeCore ≠ 0) :
    SquareFreeRat (primitiveSquareFreeDecomposition f).squareFreeCore := by
  sorry

theorem coprimeModP_of_bezout
    (f g s t : ZPoly) (p : Nat)
    (hbez : congr (s * f + t * g) 1 p) :
    coprimeModP f g p := by
  exact ⟨s, t, hbez⟩

end ZPoly
end Hex
