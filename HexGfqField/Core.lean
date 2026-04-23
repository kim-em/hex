import HexGfqRing

/-!
Core carrier scaffolding for `HexGfqField`.

This module introduces `FiniteField p f hf hirr` as a thin wrapper over
`HexGfqRing.PolyQuotient p f hf`. Phase 1 stops at the carrier and
conversion boundary: the quotient-field operations and field-law proofs
land in later issues.
-/

namespace HexGfqField

open HexPolyFp
open HexGfqRing

variable {p : Nat} [NeZero p]

/--
Scaffold irreducibility predicate for quotient-field moduli.

The executable finite-field carrier only needs a nontrivial modulus
boundary in Phase 1; later issues refine this into the intended
algebraic irreducibility story over `FpPoly`.
-/
def Irreducible (f : FpPoly p) : Prop :=
  f ≠ 0 ∧ 0 < f.degree

/--
Thin wrapper over the quotient-ring carrier `F_p[x] / (f)` under an
irreducibility hypothesis on the modulus.
-/
structure FiniteField (p : Nat) [NeZero p] (f : FpPoly p)
    (hf : 0 < f.degree) (hirr : Irreducible f) where
  /-- Underlying quotient-ring element. -/
  val : PolyQuotient p f hf

namespace FiniteField

variable {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}

/-- Build a field element from the shared quotient-ring carrier. -/
def ofQuotient (x : PolyQuotient p f hf) : FiniteField p f hf hirr :=
  ⟨x⟩

/-- Forget the irreducibility wrapper back to the shared quotient carrier. -/
def toQuotient (x : FiniteField p f hf hirr) : PolyQuotient p f hf :=
  x.val

instance : CoeOut (FiniteField p f hf hirr) (PolyQuotient p f hf) where
  coe := FiniteField.toQuotient

/-- Reduce an arbitrary polynomial into the finite-field carrier. -/
def ofPoly (a : FpPoly p) : FiniteField p f hf hirr :=
  FiniteField.ofQuotient (HexGfqRing.ofPoly (f := f) hf a)

/-- Projection to the shared canonical representative. -/
def repr (x : FiniteField p f hf hirr) : FpPoly p :=
  HexGfqRing.repr x.val

/-- Field elements are determined by their underlying quotient representatives. -/
@[ext] theorem ext {x y : FiniteField p f hf hirr} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Wrapping and immediately unwrapping a quotient element is the identity. -/
@[simp] theorem toQuotient_ofQuotient (x : PolyQuotient p f hf) :
    FiniteField.toQuotient (FiniteField.ofQuotient (hirr := hirr) x) = x := by
  rfl

/-- Every field element unwraps to the stored quotient representative. -/
@[simp] theorem ofQuotient_toQuotient (x : FiniteField p f hf hirr) :
    FiniteField.ofQuotient (hirr := hirr) (FiniteField.toQuotient x) = x := by
  cases x
  rfl

/-- Equality in the field wrapper reduces to equality in the quotient carrier. -/
theorem toQuotient_injective :
    Function.Injective (FiniteField.toQuotient (p := p) (f := f) (hf := hf) (hirr := hirr)) := by
  intro x y hxy
  exact FiniteField.ext hxy

/-- The quotient representative of `ofPoly` is the reduced remainder modulo `f`. -/
@[simp] theorem toQuotient_ofPoly (a : FpPoly p) :
    FiniteField.toQuotient (FiniteField.ofPoly (f := f) (hf := hf) (hirr := hirr) a) =
      HexGfqRing.ofPoly (f := f) hf a := by
  rfl

/-- The stored canonical representative matches the quotient-ring representative. -/
@[simp] theorem repr_ofQuotient (x : PolyQuotient p f hf) :
    FiniteField.repr (FiniteField.ofQuotient (hirr := hirr) x) = HexGfqRing.repr x := by
  rfl

/-- The representative of `ofPoly` is the reduced polynomial modulo `f`. -/
@[simp] theorem repr_ofPoly (a : FpPoly p) :
    FiniteField.repr (FiniteField.ofPoly (f := f) (hf := hf) (hirr := hirr) a) =
      HexGfqRing.reduceMod f a := by
  rfl

end FiniteField

/-- Top-level constructor from the shared quotient-ring carrier. -/
def ofQuotient {f : FpPoly p} (hf : 0 < f.degree) {hirr : Irreducible f}
    (x : PolyQuotient p f hf) : FiniteField p f hf hirr :=
  @FiniteField.ofQuotient p _ f hf hirr x

/-- Top-level projection to the underlying quotient-ring carrier. -/
def toQuotient {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x : FiniteField p f hf hirr) : PolyQuotient p f hf :=
  x.val

/-- Top-level constructor reducing an arbitrary polynomial modulo `f`. -/
def ofPoly {f : FpPoly p} (hf : 0 < f.degree) {hirr : Irreducible f}
    (a : FpPoly p) : FiniteField p f hf hirr :=
  @FiniteField.ofPoly p _ f hf hirr a

/-- Top-level projection to the shared canonical representative. -/
def repr {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x : FiniteField p f hf hirr) : FpPoly p :=
  @FiniteField.repr p _ f hf hirr x

/-- Top-level quotient round trip from the field wrapper. -/
@[simp] theorem ofQuotient_toQuotient {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (x : FiniteField p f hf hirr) :
    HexGfqField.ofQuotient (f := f) hf (HexGfqField.toQuotient x) = x := by
  exact FiniteField.ofQuotient_toQuotient (hirr := hirr) x

/-- Top-level quotient round trip into the field wrapper. -/
@[simp] theorem toQuotient_ofQuotient {f : FpPoly p} (hf : 0 < f.degree) {hirr : Irreducible f}
    (x : PolyQuotient p f hf) :
    HexGfqField.toQuotient (HexGfqField.ofQuotient (f := f) (hirr := hirr) hf x) = x := by
  rfl

/-- The top-level representative of `ofPoly` is the reduced remainder modulo `f`. -/
@[simp] theorem repr_ofPoly {f : FpPoly p} {hf : 0 < f.degree} {hirr : Irreducible f}
    (a : FpPoly p) :
    HexGfqField.repr (HexGfqField.ofPoly (f := f) (hirr := hirr) hf a) =
      HexGfqRing.reduceMod f a := by
  rfl

end HexGfqField
