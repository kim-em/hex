import HexBerlekamp.Kernel

/-!
Executable factor-splitting scaffolding for `HexBerlekamp`.

This module adds the next public Phase 1 boundary after the Berlekamp
matrix/kernel surface: a single Berlekamp split step driven by
`gcd(f, h - c)` for a chosen kernel element `h` and split constant `c`.
The executable layer introduces a public result record together with a
deterministic search over constants in `F_p`, while the theorem layer
records the intended factorization contract for later phases.
-/

namespace HexBerlekamp

open HexModArith

variable {p : Nat} [NeZero p]

local instance instDecidableEqFpPoly : DecidableEq (HexPolyFp.FpPoly p) := by
  intro f g
  cases f with
  | mk coeffsF normalizedF =>
      cases g with
      | mk coeffsG normalizedG =>
          by_cases h : coeffsF = coeffsG
          · subst h
            exact isTrue rfl
          · exact isFalse (fun hfg => h (by cases hfg; rfl))

/--
Executable coefficient division for `ZMod64 p`.

This reuses the partial inverse shell from `HexModArith`, matching the
existing `HexPolyFp` executable GCD boundary.
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

/-- Public output of one Berlekamp factor-splitting attempt. -/
structure SplitResult (p : Nat) [NeZero p] where
  kernelElement : HexPolyFp.FpPoly p
  splitConstant : HexModArith.ZMod64 p
  splitPolynomial : HexPolyFp.FpPoly p
  leftFactor : HexPolyFp.FpPoly p
  rightFactor : HexPolyFp.FpPoly p

/-- The candidate splitter polynomial `h - c` used by Berlekamp's method. -/
def splitPolynomial (h : HexPolyFp.FpPoly p) (c : HexModArith.ZMod64 p) :
    HexPolyFp.FpPoly p :=
  HexPolyFp.FpPoly.sub h (HexPolyFp.FpPoly.C c)

/-- The left factor candidate returned by the `gcd(f, h - c)` split step. -/
def splitFactorLeft (f h : HexPolyFp.FpPoly p) (c : HexModArith.ZMod64 p) :
    HexPolyFp.FpPoly p :=
  gcd f (splitPolynomial (p := p) h c)

/-- The right factor candidate obtained by dividing `f` by the gcd split factor. -/
def splitFactorRight (f h : HexPolyFp.FpPoly p) (c : HexModArith.ZMod64 p) :
    HexPolyFp.FpPoly p :=
  divBy f (splitFactorLeft (p := p) f h c)

/-- Package the executable `gcd(f, h - c)` split attempt for a fixed constant. -/
def splitWithConstant (f h : HexPolyFp.FpPoly p) (c : HexModArith.ZMod64 p) :
    SplitResult p :=
  { kernelElement := h
    splitConstant := c
    splitPolynomial := splitPolynomial (p := p) h c
    leftFactor := splitFactorLeft (p := p) f h c
    rightFactor := splitFactorRight (p := p) f h c }

/--
The split is nontrivial against `f` when the returned gcd is neither
`0`, `1`, nor the whole polynomial.
-/
def SplitResult.NontrivialAgainst (result : SplitResult p) (f : HexPolyFp.FpPoly p) : Prop :=
  result.leftFactor ≠ 0 ∧
    result.leftFactor ≠ HexPolyFp.FpPoly.C (1 : HexModArith.ZMod64 p) ∧
    result.leftFactor ≠ f

/-- Executable boolean test for the nontrivial split side conditions. -/
def SplitResult.isNontrivialAgainst (result : SplitResult p) (f : HexPolyFp.FpPoly p) : Bool :=
  decide (result.leftFactor ≠ 0) &&
    decide (result.leftFactor ≠ HexPolyFp.FpPoly.C (1 : HexModArith.ZMod64 p)) &&
    decide (result.leftFactor ≠ f)

/-- Search the field constants in order for the first nontrivial split. -/
private def splitSearch (f h : HexPolyFp.FpPoly p) : List Nat → Option (SplitResult p)
  | [] => none
  | n :: ns =>
      let c : HexModArith.ZMod64 p := n
      let result := splitWithConstant (p := p) f h c
      if result.isNontrivialAgainst f then
        some result
      else
        splitSearch f h ns

/--
Executable single-step Berlekamp split search.

Given a candidate kernel element `h`, search all constants `c ∈ F_p` in
ascending representative order and return the first nontrivial
`gcd(f, h - c)` split, if any.
-/
def berlekampSplitStep (f h : HexPolyFp.FpPoly p) : Option (SplitResult p) :=
  splitSearch (p := p) f h (List.range p)

/-- `splitWithConstant` stores the advertised `h - c` splitter polynomial. -/
theorem splitWithConstant_splitPolynomial (f h : HexPolyFp.FpPoly p) (c : HexModArith.ZMod64 p) :
    (splitWithConstant (p := p) f h c).splitPolynomial =
      splitPolynomial (p := p) h c := by
  rfl

/-- `splitWithConstant` records the gcd branch as its left factor. -/
theorem splitWithConstant_leftFactor (f h : HexPolyFp.FpPoly p) (c : HexModArith.ZMod64 p) :
    (splitWithConstant (p := p) f h c).leftFactor =
      gcd f (splitPolynomial (p := p) h c) := by
  rfl

/-- `splitWithConstant` records the quotient-by-gcd branch as its right factor. -/
theorem splitWithConstant_rightFactor (f h : HexPolyFp.FpPoly p) (c : HexModArith.ZMod64 p) :
    (splitWithConstant (p := p) f h c).rightFactor =
      divBy f (gcd f (splitPolynomial (p := p) h c)) := by
  rfl

/-- The boolean nontriviality test reflects the proposition-level split side conditions. -/
theorem SplitResult.isNontrivialAgainst_eq_true_iff (result : SplitResult p) (f : HexPolyFp.FpPoly p) :
    result.isNontrivialAgainst f = true ↔ result.NontrivialAgainst f := by
  sorry

/--
When a split attempt is packaged for a fixed constant, its returned
factors are intended to reconstruct the input polynomial.
-/
theorem splitWithConstant_mul_rightFactor (f h : HexPolyFp.FpPoly p) (c : HexModArith.ZMod64 p) :
    let result := splitWithConstant (p := p) f h c
    result.leftFactor * result.rightFactor = f := by
  sorry

/--
Any successful `berlekampSplitStep` returns a nontrivial `gcd(f, h - c)`
factorization candidate.
-/
theorem berlekampSplitStep_nontrivial (f h : HexPolyFp.FpPoly p) :
    ∀ result, berlekampSplitStep (p := p) f h = some result →
      result.NontrivialAgainst f := by
  sorry

/--
Any successful `berlekampSplitStep` records a factor pair whose product
is intended to recover the original polynomial.
-/
theorem berlekampSplitStep_product (f h : HexPolyFp.FpPoly p) :
    ∀ result, berlekampSplitStep (p := p) f h = some result →
      result.leftFactor * result.rightFactor = f := by
  sorry

end HexBerlekamp
