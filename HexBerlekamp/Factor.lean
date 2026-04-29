import HexBerlekamp.Basic

/-!
Executable Berlekamp split-step factoring for `hex-berlekamp`.

This module adds the factoring-facing surface promised by the spec. It first
exposes the single-witness split primitive `gcd(f, h - c)`, then builds the
public Berlekamp factorization driver by computing the fixed-space kernel once
and repeatedly applying those witnesses to the current factor list.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- Result of one Berlekamp kernel-witness split search. -/
structure SplitResult (p : Nat) [ZMod64.Bounds p] where
  splitConstant : ZMod64 p
  factor : FpPoly p
  cofactor : FpPoly p

/-- Public result of executable Berlekamp factorization. -/
structure Factorization (p : Nat) [ZMod64.Bounds p] where
  input : FpPoly p
  factors : List (FpPoly p)

/-- Multiply a list of `F_p[x]` factors in stored order. -/
def factorProduct (factors : List (FpPoly p)) : FpPoly p :=
  factors.foldl (fun acc factor => acc * factor) 1

/-- Product of the factors returned by a `Factorization`. -/
def Factorization.product (result : Factorization p) : FpPoly p :=
  factorProduct result.factors

/-- The gcd candidate attached to one field constant `c`. -/
def splitFactorAt (f witness : FpPoly p) (c : ZMod64 p) : FpPoly p :=
  DensePoly.gcd f (witness - FpPoly.C c)

/-- `true` exactly when the gcd candidate is neither `0`, `1`, nor all of `f`. -/
private def isNontrivialSplitFactor (f g : FpPoly p) : Bool :=
  !g.isZero && g ≠ 1 && g ≠ f

/-- Search the constants `0, 1, ..., p - 1` for a nontrivial Berlekamp split. -/
private def kernelWitnessSplitAux (f witness : FpPoly p) : Nat → Nat → Option (SplitResult p)
  | 0, _ => none
  | fuel + 1, c =>
      let splitConstant := ZMod64.ofNat p c
      let factor := splitFactorAt f witness splitConstant
      if isNontrivialSplitFactor f factor then
        some
          { splitConstant
            factor
            cofactor := f / factor }
      else
        kernelWitnessSplitAux f witness fuel (c + 1)

/--
Search the Berlekamp split candidates `gcd(f, h - c)` over all constants
`c : F_p`, returning the first nontrivial factorization found.
-/
def kernelWitnessSplit? (f witness : FpPoly p) : Option (SplitResult p) :=
  kernelWitnessSplitAux f witness p 0

/-- Try a list of kernel witnesses against one current factor. -/
private def splitWithWitnesses? (f : FpPoly p) : List (FpPoly p) → Option (SplitResult p)
  | [] => none
  | witness :: witnesses =>
      match kernelWitnessSplit? f witness with
      | some split => some split
      | none => splitWithWitnesses? f witnesses

/-- Split the first factor in the list that admits a Berlekamp witness split. -/
private def splitFirstFactor? (witnesses : List (FpPoly p)) :
    List (FpPoly p) → Option (List (FpPoly p))
  | [] => none
  | factor :: rest =>
      match splitWithWitnesses? factor witnesses with
      | some split => some (split.factor :: split.cofactor :: rest)
      | none =>
          match splitFirstFactor? witnesses rest with
          | some rest' => some (factor :: rest')
          | none => none

/--
Repeatedly split the current factor list using the fixed-space witnesses.
The fuel bounds the executable loop; for square-free input, every successful
split increases the factor count and the natural bound is the input size.
-/
private def berlekampFactorLoop (witnesses : List (FpPoly p)) :
    Nat → List (FpPoly p) → List (FpPoly p)
  | 0, factors => factors
  | fuel + 1, factors =>
      match splitFirstFactor? witnesses factors with
      | some factors' => berlekampFactorLoop witnesses fuel factors'
      | none => factors

/--
Compute the Berlekamp factorization of a monic polynomial over `F_p` by
building the fixed-space kernel of `Q_f - I` and repeatedly splitting current
factors with the resulting kernel representatives.
-/
def berlekampFactor (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] : Factorization p :=
  let witnesses := (fixedSpaceKernel f hmonic).toList
  { input := f
    factors := berlekampFactorLoop witnesses (f.size + 1) [f] }

theorem splitFactorAt_spec (f witness : FpPoly p) (c : ZMod64 p) :
    splitFactorAt f witness c = DensePoly.gcd f (witness - FpPoly.C c) := by
  rfl

/--
Any successful Berlekamp split records a factor and cofactor whose product is
the original polynomial.
-/
theorem kernelWitnessSplit_product_spec
    (f witness : FpPoly p) (r : SplitResult p)
    (hsplit : kernelWitnessSplit? f witness = some r) :
    r.factor * r.cofactor = f := by
  sorry

/--
Any successful Berlekamp split is nontrivial: the returned factor is neither
`0`, `1`, nor the full input polynomial.
-/
theorem kernelWitnessSplit_nontrivial
    (f witness : FpPoly p) (r : SplitResult p)
    (hsplit : kernelWitnessSplit? f witness = some r) :
    !r.factor.isZero ∧ r.factor ≠ 1 ∧ r.factor ≠ f := by
  sorry

/--
The executable Berlekamp factorization preserves the input polynomial as the
product of the returned factors for square-free monic inputs.
-/
theorem prod_berlekampFactor
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)]
    (_hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    (berlekampFactor f hmonic).product = f := by
  sorry

end Berlekamp

end Hex
