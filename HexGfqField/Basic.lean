import HexGfqRing.Operations

/-!
Core finite-field wrapper definitions for executable `F_p[x] / (f)`.

This module packages the quotient-ring representation from `HexGfqRing`
into the spec-named `FiniteField` type, keeping the same reduced
representatives and exposing explicit conversions back to the quotient and
polynomial views.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- Polynomial irreducibility over `F_p` phrased as the absence of nontrivial
factorizations inside the executable dense-polynomial model. -/
def Irreducible (f : FpPoly p) : Prop :=
  f ≠ 0 ∧ ∀ a b : FpPoly p, a * b = f → FpPoly.degree a = 0 ∨ FpPoly.degree b = 0

end FpPoly

namespace GFqField

variable {p : Nat} [ZMod64.Bounds p]

/-- Executable finite-field elements are a thin wrapper around quotient-ring
residues modulo an irreducible polynomial. -/
structure FiniteField
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (_hirr : FpPoly.Irreducible f) where
  toQuotient : GFqRing.PolyQuotient f hf

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    DecidableEq (FiniteField f hf hirr) := by
  intro x y
  match decEq x.toQuotient y.toQuotient with
  | isTrue h =>
      exact isTrue (by
        cases x
        cases y
        cases h
        rfl)
  | isFalse h =>
      exact isFalse (by
        intro hxy
        apply h
        exact congrArg FiniteField.toQuotient hxy)

/-- Wrap a quotient-ring element as a finite-field element. -/
def ofQuotient {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : GFqRing.PolyQuotient f hf) : FiniteField f hf hirr :=
  ⟨x⟩

/-- Reduce a polynomial into the finite field by reusing the quotient-ring
constructor. -/
def ofPoly (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f)
    (g : FpPoly p) : FiniteField f hf hirr :=
  ofQuotient (GFqRing.ofPoly f hf g)

/-- Project a finite-field element to its canonical polynomial representative. -/
def repr {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) : FpPoly p :=
  GFqRing.repr x.toQuotient

@[simp] theorem toQuotient_ofQuotient
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : GFqRing.PolyQuotient f hf) :
    (ofQuotient x : FiniteField f hf hirr).toQuotient = x :=
  rfl

@[simp] theorem toQuotient_ofPoly
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) (g : FpPoly p) :
    (ofPoly f hf hirr g).toQuotient = GFqRing.ofPoly f hf g :=
  rfl

@[simp] theorem repr_ofPoly
    (f : FpPoly p) (hf : 0 < FpPoly.degree f) (hirr : FpPoly.Irreducible f) (g : FpPoly p) :
    repr (ofPoly f hf hirr g) = GFqRing.reduceMod f g :=
  rfl

@[simp] theorem degree_repr_lt_degree
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    (x : FiniteField f hf hirr) :
    FpPoly.degree (repr x) < FpPoly.degree f :=
  GFqRing.degree_repr_lt_degree x.toQuotient

@[ext] theorem ext
    {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f}
    {x y : FiniteField f hf hirr} (h : x.toQuotient = y.toQuotient) :
    x = y := by
  cases x
  cases y
  cases h
  rfl

end GFqField
end Hex
