import HexHensel.Multifactor

/-!
Executable data records for the Berlekamp-Zassenhaus factorization pipeline.

This module contains the shared records passed between prime selection,
Hensel lifting, and integer recombination in the `ZPoly` factorization
pipeline.
-/
namespace Hex

namespace ZPoly

private def intModNat (z : Int) (m : Nat) : Nat :=
  Int.toNat (z % Int.ofNat m)

/-- The integer leading coefficient reduced to the candidate prime field. -/
def leadingCoeffModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : ZMod64 p :=
  ZMod64.ofNat p (intModNat (DensePoly.leadingCoeff f) p)

end ZPoly

/-- The candidate prime does not divide the integer leading coefficient. -/
def leadingCoeffAdmissible (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Prop :=
  ZPoly.leadingCoeffModP f p ≠ 0

/-- The modular image is square-free according to the executable gcd criterion. -/
def squareFreeModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Prop :=
  let fModP := ZPoly.modP p f
  DensePoly.gcd fModP (DensePoly.derivative fModP) = 1

/--
Executable good-prime predicate for the Berlekamp-Zassenhaus pipeline.

It checks that the modulus is nontrivial, that the integer leading coefficient
survives reduction modulo `p`, and that the modular image is square-free.
-/
def isGoodPrime (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Bool :=
  let fModP := ZPoly.modP p f
  p > 1 &&
    ZPoly.leadingCoeffModP f p != 0 &&
    DensePoly.gcd fModP (DensePoly.derivative fModP) == 1

private theorem bounds_two : ZMod64.Bounds 2 := by
  constructor <;> decide

private theorem bounds_three : ZMod64.Bounds 3 := by
  constructor <;> decide

private theorem bounds_five : ZMod64.Bounds 5 := by
  constructor <;> decide

private theorem bounds_seven : ZMod64.Bounds 7 := by
  constructor <;> decide

private theorem bounds_eleven : ZMod64.Bounds 11 := by
  constructor <;> decide

private theorem bounds_thirteen : ZMod64.Bounds 13 := by
  constructor <;> decide

private theorem bounds_seventeen : ZMod64.Bounds 17 := by
  constructor <;> decide

private theorem bounds_nineteen : ZMod64.Bounds 19 := by
  constructor <;> decide

private theorem prime_two : Nat.Prime 2 := by
  sorry

private theorem prime_three : Nat.Prime 3 := by
  sorry

private theorem prime_five : Nat.Prime 5 := by
  sorry

private theorem prime_seven : Nat.Prime 7 := by
  sorry

private theorem prime_eleven : Nat.Prime 11 := by
  sorry

private theorem prime_thirteen : Nat.Prime 13 := by
  sorry

private theorem prime_seventeen : Nat.Prime 17 := by
  sorry

private theorem prime_nineteen : Nat.Prime 19 := by
  sorry

private structure SmallPrimeCandidate where
  p : Nat
  bounds : ZMod64.Bounds p
  prime : Nat.Prime p

/-- A scored admissible small-prime candidate for default prime selection. -/
structure PrimeCandidateScore where
  /-- Candidate prime. -/
  p : Nat
  /-- Smaller scores are preferred; equal scores retain the earlier smaller prime. -/
  factorCount : Nat

private def smallPrimeCandidates : List SmallPrimeCandidate :=
  [ { p := 2, bounds := bounds_two, prime := prime_two },
    { p := 3, bounds := bounds_three, prime := prime_three },
    { p := 5, bounds := bounds_five, prime := prime_five },
    { p := 7, bounds := bounds_seven, prime := prime_seven },
    { p := 11, bounds := bounds_eleven, prime := prime_eleven },
    { p := 13, bounds := bounds_thirteen, prime := prime_thirteen },
    { p := 17, bounds := bounds_seventeen, prime := prime_seventeen },
    { p := 19, bounds := bounds_nineteen, prime := prime_nineteen } ]

private def scoreCandidate (f : ZPoly) (c : SmallPrimeCandidate) : Option PrimeCandidateScore :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let fModP := ZPoly.modP c.p f
    let factors := (FpPoly.squareFreeDecomposition c.prime fModP).factors
    some { p := c.p, factorCount := factors.length }
  else
    none

private def betterScore (old new : PrimeCandidateScore) : PrimeCandidateScore :=
  if new.factorCount < old.factorCount then
    new
  else
    old

/-- Scan the fixed small-prime list and return the best admissible scored candidate, if any. -/
def choosePrimeScore? (f : ZPoly) : Option PrimeCandidateScore :=
  smallPrimeCandidates.foldl
    (fun best c =>
      match best, scoreCandidate f c with
      | none, score => score
      | some old, none => some old
      | some old, some new => some (betterScore old new))
    none

/--
Choose a small admissible prime for the Berlekamp-Zassenhaus pipeline.

The search is bounded to a fixed ascending list of small primes. Candidate
scores use the currently available executable modular factor surface; strict
score improvement replaces the incumbent, so equal scores keep the smaller
earlier prime.
-/
def choosePrime (f : ZPoly) : Nat :=
  match choosePrimeScore? f with
  | some score => score.p
  | none => 2

theorem choosePrimeScore?_isGoodPrime
    (f : ZPoly) (score : PrimeCandidateScore)
    (hscore : choosePrimeScore? f = some score) :
    ∃ hbounds : ZMod64.Bounds score.p,
      @isGoodPrime f score.p hbounds = true := by
  sorry

theorem choosePrime_isGoodPrime_of_selected
    (f : ZPoly) (score : PrimeCandidateScore)
    (hscore : choosePrimeScore? f = some score)
    (hchoose : choosePrime f = score.p) :
    ∃ hbounds : ZMod64.Bounds (choosePrime f),
      @isGoodPrime f (choosePrime f) hbounds = true := by
  sorry

/-- A successful good-prime check certifies leading-coefficient admissibility. -/
theorem isGoodPrime_leadingCoeffAdmissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    leadingCoeffAdmissible f p := by
  sorry

/-- A successful good-prime check certifies the modular square-free precondition. -/
theorem isGoodPrime_squareFreeModP
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    squareFreeModP f p := by
  sorry

/--
Data produced by modular prime selection: the selected prime, the image of the
input polynomial over that prime field, and its modular factors.
-/
structure PrimeChoiceData where
  p : Nat
  [bounds : ZMod64.Bounds p]
  fModP : FpPoly p
  factorsModP : Array (FpPoly p)

/--
Data produced by Hensel lifting and consumed by integer recombination: the
prime, the requested lift precision, and the lifted integer factors.
-/
structure LiftData where
  p : Nat
  k : Nat
  liftedFactors : Array ZPoly

private structure PrimeChoiceDataScore where
  data : PrimeChoiceData
  factorCount : Nat

private def primeChoiceDataScore (f : ZPoly) (c : SmallPrimeCandidate) :
    Option PrimeChoiceDataScore :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let fModP := ZPoly.modP c.p f
    let decomposition := FpPoly.squareFreeDecomposition c.prime fModP
    let factorsModP := decomposition.factors.map (fun factor => factor.factor) |>.toArray
    some
      { data := { p := c.p, fModP, factorsModP }
        factorCount := factorsModP.size }
  else
    none

private def betterPrimeChoiceDataScore
    (old new : PrimeChoiceDataScore) : PrimeChoiceDataScore :=
  if new.factorCount < old.factorCount then
    new
  else
    old

private def choosePrimeData? (f : ZPoly) : Option PrimeChoiceData :=
  smallPrimeCandidates.foldl
    (fun best c =>
      match best, primeChoiceDataScore f c with
      | none, score => score
      | some old, none => some old
      | some old, some new => some (betterPrimeChoiceDataScore old new))
    none
  |>.map (fun score => score.data)

private def fallbackPrimeChoiceData (f : ZPoly) : PrimeChoiceData :=
  letI := bounds_two
  let fModP := ZPoly.modP 2 f
  let decomposition := FpPoly.squareFreeDecomposition prime_two fModP
  let factorsModP := decomposition.factors.map (fun factor => factor.factor) |>.toArray
  { p := 2, fModP, factorsModP }

/--
Choose an admissible small prime and package the modular image together with
its square-free factor data for the rest of the pipeline.
-/
def choosePrimeData (f : ZPoly) : PrimeChoiceData :=
  match choosePrimeData? f with
  | some data => data
  | none => fallbackPrimeChoiceData f

/--
Lift the chosen modular factors to the requested precision for integer
recombination.
-/
def henselLiftData (f : ZPoly) (B : Nat) (d : PrimeChoiceData) : LiftData :=
  letI := d.bounds
  let factors := d.factorsModP.map (fun factor => FpPoly.liftToZ factor)
  { p := d.p
    k := B
    liftedFactors := ZPoly.multifactorLift d.p B f factors }

/--
Conservative integer recombination. Lifted local factors are accepted exactly
when their ordered product is already the input; otherwise the input remains as
one irreducible-for-this-pass factor.
-/
def recombine (f : ZPoly) (d : LiftData) : Array ZPoly :=
  if Array.polyProduct d.liftedFactors = f then
    d.liftedFactors
  else
    #[f]

/-- Factor with an explicit coefficient bound for the recombination stage. -/
def factorWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  let primeData := choosePrimeData f
  let liftData := henselLiftData f B primeData
  recombine f liftData

/-- Factor using the library's conservative executable coefficient bound. -/
def factor (f : ZPoly) : Array ZPoly :=
  factorWithBound f (ZPoly.coeffL2NormBound f)

/--
Conditional product contract for the bounded factorization entry point.
The bound hypothesis is the computational correctness assumption supplied by
the later proof layer.
-/
theorem factor_product_of_bound (f : ZPoly) (B : Nat)
    (hB : ∀ g : ZPoly, g ∣ f → ∀ i, (g.coeff i).natAbs ≤ B) :
    Array.foldl (· * ·) 1 (factorWithBound f B) = f := by
  sorry

end Hex
