import HexBerlekamp.Splitting

/-!
Executable distinct-degree factorization scaffolding for `HexBerlekamp`.

This module adds the next public Phase 1 boundary after the single-step
split scaffold: degree-bucket extraction driven by the standard
`gcd(f, X^(p^d) - X)` witness polynomials. The executable layer packages
each bucket attempt together with the corresponding Frobenius witness and
quotient-by-gcd cofactor, while the theorem layer records the intended
factorization contract for later phases.
-/

namespace HexBerlekamp

open HexModArith

variable {p : Nat} [NeZero p]

/--
Executable coefficient division for `ZMod64 p`.

This matches the coefficient-division shell already used by the
Berlekamp split and Rabin scaffolds.
-/
private def coeffDiv (a b : HexModArith.ZMod64 p) : HexModArith.ZMod64 p :=
  match HexModArith.ZMod64.inv? b with
  | some bInv => a * bInv
  | none => 0

/-- Polynomial division over `FpPoly` using the executable coefficient inverse shell. -/
private def divBy (f g : HexPolyFp.FpPoly p) : HexPolyFp.FpPoly p := by
  let _ : Div (HexModArith.ZMod64 p) := ⟨coeffDiv (p := p)⟩
  exact HexPoly.DensePoly.div (R := HexModArith.ZMod64 p) f g

/-- Polynomial gcd over `FpPoly` using the executable coefficient inverse shell. -/
private def gcd (f g : HexPolyFp.FpPoly p) : HexPolyFp.FpPoly p := by
  let _ : Div (HexModArith.ZMod64 p) := ⟨coeffDiv (p := p)⟩
  exact HexPoly.DensePoly.gcd (R := HexModArith.ZMod64 p) f g

/--
One distinct-degree bucket attempt for a fixed positive degree `d`.

The intended interpretation is that `extractedFactor` contains the
product of the factors of `f` whose irreducible degrees divide `d`,
while `remainingFactor` stores the corresponding quotient shell.
-/
structure DistinctDegreeBucket (p : Nat) [NeZero p] where
  degreeIndex : Nat
  frobeniusWitness : HexPolyFp.FpPoly p
  splitPolynomial : HexPolyFp.FpPoly p
  extractedFactor : HexPolyFp.FpPoly p
  remainingFactor : HexPolyFp.FpPoly p

/-- Public output of the current distinct-degree factorization scaffold. -/
structure DistinctDegreeFactorizationResult (p : Nat) [NeZero p] where
  source : HexPolyFp.FpPoly p
  buckets : List (DistinctDegreeBucket p)

/--
The canonical distinct-degree witness polynomial `X^(p^d) - X (mod f)`.
-/
def distinctDegreeSplitPolynomial (f : HexPolyFp.FpPoly p) (d : Nat) :
    HexPolyFp.FpPoly p :=
  HexPolyFp.FpPoly.sub
    (HexPolyFp.FpPoly.frobeniusPowModMonic HexPolyFp.FpPoly.X f d)
    HexPolyFp.FpPoly.X

/--
Package the executable `gcd(f, X^(p^d) - X)` bucket extraction for a
fixed degree `d`.
-/
def extractDistinctDegreeBucket (f : HexPolyFp.FpPoly p) (d : Nat) :
    DistinctDegreeBucket p :=
  let witness := HexPolyFp.FpPoly.frobeniusPowModMonic HexPolyFp.FpPoly.X f d
  let splitPolynomial := distinctDegreeSplitPolynomial (p := p) f d
  let extractedFactor := gcd f splitPolynomial
  { degreeIndex := d
    frobeniusWitness := witness
    splitPolynomial := splitPolynomial
    extractedFactor := extractedFactor
    remainingFactor := divBy f extractedFactor }

/--
Enumerate the first-pass degree buckets `d = 1, ..., deg(f)` against the
current polynomial `f`.
-/
def distinctDegreeBuckets (f : HexPolyFp.FpPoly p) : List (DistinctDegreeBucket p) :=
  (List.range f.degree).map fun k => extractDistinctDegreeBucket (p := p) f (k + 1)

/--
Public distinct-degree factorization entry point.

The current scaffold records the source polynomial together with the
ordered bucket extractions for degrees `1` through `deg(f)`.
-/
def distinctDegreeFactorization (f : HexPolyFp.FpPoly p) :
    DistinctDegreeFactorizationResult p :=
  { source := f
    buckets := distinctDegreeBuckets (p := p) f }

/--
`extractDistinctDegreeBucket` stores the advertised Frobenius witness
`X^(p^d) mod f`.
-/
theorem extractDistinctDegreeBucket_frobeniusWitness (f : HexPolyFp.FpPoly p) (d : Nat) :
    (extractDistinctDegreeBucket (p := p) f d).frobeniusWitness =
      HexPolyFp.FpPoly.frobeniusPowModMonic HexPolyFp.FpPoly.X f d := by
  rfl

/--
`extractDistinctDegreeBucket` stores the advertised witness polynomial
`X^(p^d) - X (mod f)`.
-/
theorem extractDistinctDegreeBucket_splitPolynomial (f : HexPolyFp.FpPoly p) (d : Nat) :
    (extractDistinctDegreeBucket (p := p) f d).splitPolynomial =
      distinctDegreeSplitPolynomial (p := p) f d := by
  rfl

/-- `extractDistinctDegreeBucket` records the `gcd(f, X^(p^d) - X)` branch as its extracted factor. -/
theorem extractDistinctDegreeBucket_extractedFactor (f : HexPolyFp.FpPoly p) (d : Nat) :
    (extractDistinctDegreeBucket (p := p) f d).extractedFactor =
      gcd f (distinctDegreeSplitPolynomial (p := p) f d) := by
  rfl

/-- `extractDistinctDegreeBucket` records the quotient-by-gcd branch as its remaining factor. -/
theorem extractDistinctDegreeBucket_remainingFactor (f : HexPolyFp.FpPoly p) (d : Nat) :
    (extractDistinctDegreeBucket (p := p) f d).remainingFactor =
      divBy f (gcd f (distinctDegreeSplitPolynomial (p := p) f d)) := by
  rfl

/--
Each bucket extraction is intended to package a factor/cofactor pair
whose product reconstructs the input polynomial.
-/
theorem extractDistinctDegreeBucket_product (f : HexPolyFp.FpPoly p) (d : Nat) :
    let result := extractDistinctDegreeBucket (p := p) f d
    result.extractedFactor * result.remainingFactor = f := by
  sorry

/--
The public factorization entry point preserves the source polynomial in
its result record.
-/
theorem distinctDegreeFactorization_source (f : HexPolyFp.FpPoly p) :
    (distinctDegreeFactorization (p := p) f).source = f := by
  rfl

/--
The initial distinct-degree scaffold emits one bucket attempt for each
degree `1, ..., deg(f)`.
-/
theorem distinctDegreeFactorization_buckets_length (f : HexPolyFp.FpPoly p) :
    (distinctDegreeFactorization (p := p) f).buckets.length = f.degree := by
  simp [distinctDegreeFactorization, distinctDegreeBuckets]

/--
Every bucket reported by `distinctDegreeFactorization` is intended to
store the corresponding `gcd(f, X^(p^d) - X)` extraction data for its
recorded degree index.
-/
theorem distinctDegreeFactorization_bucket_spec (f : HexPolyFp.FpPoly p) :
    ∀ bucket ∈ (distinctDegreeFactorization (p := p) f).buckets,
      bucket.splitPolynomial =
          distinctDegreeSplitPolynomial (p := p) f bucket.degreeIndex ∧
        bucket.extractedFactor = gcd f bucket.splitPolynomial := by
  sorry

end HexBerlekamp
