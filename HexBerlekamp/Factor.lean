import HexBerlekamp.Basic

/-!
Executable Berlekamp split-step factoring for `hex-berlekamp`.

This module adds the first factoring-facing surface promised by the spec:
given a monic polynomial `f : FpPoly p` and a kernel witness `h` from the
fixed space of `Q_f - I`, search the field constants `c : F_p` for a
nontrivial gcd `gcd(f, h - c)`. A successful search returns the split factor,
its cofactor, and the constant that produced the split.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- Result of one Berlekamp kernel-witness split search. -/
structure SplitResult (p : Nat) [ZMod64.Bounds p] where
  splitConstant : ZMod64 p
  factor : FpPoly p
  cofactor : FpPoly p

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

end Berlekamp

end Hex
