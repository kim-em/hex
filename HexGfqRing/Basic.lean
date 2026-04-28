import HexPolyFp.Basic

/-!
Core quotient-representation definitions for executable `F_p[x] / (f)`.

This module introduces the canonical reduction function together with the
quotient-element wrapper that stores reduced representatives modulo a fixed
nonconstant polynomial.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

/-- Division in `ZMod64 p` uses the existing executable inverse candidate. -/
instance : Div (ZMod64 p) where
  div a b := a * b⁻¹

end ZMod64

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- The degree of a polynomial, defaulting to `0` for the zero polynomial. -/
def degree (f : FpPoly p) : Nat :=
  f.degree?.getD 0

end FpPoly

namespace GFqRing

variable {p : Nat} [ZMod64.Bounds p]

/-- Canonical remainder reduction modulo `f`, using the existing division surface. -/
def reduceMod (f : FpPoly p) : FpPoly p → FpPoly p :=
  fun g => (Hex.DensePoly.divMod g f).2

/-- Polynomials already known to be canonical representatives modulo `f`. -/
def IsReduced (f : FpPoly p) (g : FpPoly p) : Prop :=
  ∃ h : FpPoly p, g = reduceMod f h

/-- Executable quotient elements represented by canonical reduced polynomials. -/
abbrev PolyQuotient (f : FpPoly p) (_hf : 0 < FpPoly.degree f) :=
  { g : FpPoly p // IsReduced f g }

/-- Inject a polynomial into the quotient by reducing it modulo `f`. -/
def ofPoly (f : FpPoly p) (hf : 0 < FpPoly.degree f) (g : FpPoly p) :
    PolyQuotient f hf :=
  ⟨reduceMod f g, ⟨g, rfl⟩⟩

/-- Project a quotient element to its canonical polynomial representative. -/
def repr {f : FpPoly p} {hf : 0 < FpPoly.degree f} (x : PolyQuotient f hf) : FpPoly p :=
  x.1

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} : DecidableEq (PolyQuotient f hf) := by
  intro x y
  match decEq x.1 y.1 with
  | isTrue h => exact isTrue (Subtype.ext h)
  | isFalse h => exact isFalse (fun hxy => h (congrArg Subtype.val hxy))

@[simp] theorem repr_ofPoly (f : FpPoly p) (hf : 0 < FpPoly.degree f) (g : FpPoly p) :
    repr (ofPoly f hf g) = reduceMod f g :=
  rfl

theorem degree_repr_lt_degree {f : FpPoly p} {hf : 0 < FpPoly.degree f}
    (x : PolyQuotient f hf) :
    FpPoly.degree (repr x) < FpPoly.degree f := by
  sorry

theorem reduceMod_idem (f : FpPoly p) (g : FpPoly p) :
    reduceMod f (reduceMod f g) = reduceMod f g := by
  sorry

theorem ofPoly_reduceMod (f : FpPoly p) (hf : 0 < FpPoly.degree f) (g : FpPoly p) :
    ofPoly f hf (reduceMod f g) = ofPoly f hf g := by
  apply Subtype.ext
  simp [ofPoly, reduceMod_idem]

end GFqRing
end Hex
