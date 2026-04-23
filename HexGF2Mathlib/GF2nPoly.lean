import Mathlib.Algebra.Ring.Equiv
import HexGF2.GF2nPoly
import HexGF2Mathlib.GF2Poly
import HexGfqField

/-!
Mathlib bridge scaffolding for the large-degree `GF2nPoly` carrier.

This module adds the first bridge boundary promised by the Phase 1 spec for
packed multi-word `GF(2^n)` elements: the transported modulus in
`HexPolyFp.FpPoly 2`, conversion functions between `HexGF2.GF2nPoly` and the
generic quotient-field wrapper from `HexGfqField`, and the scaffolded ring
equivalence declaration built on top of those conversions.
-/

namespace HexGF2

namespace GF2nPoly

open HexModArith

variable {f : GF2Poly} {hirr : GF2Poly.Irreducible f}

/-- The generic `FpPoly 2` modulus corresponding to the packed irreducible polynomial. -/
def fpModulus (f : GF2Poly) : HexPolyFp.FpPoly 2 :=
  GF2Poly.toFpPoly f

/-- Packed irreducibility should transport to the generic `FpPoly 2` modulus. -/
theorem fpModulus_irreducible (hirr : GF2Poly.Irreducible f) :
    HexGfqField.Irreducible (fpModulus f) := by
  let _ := hirr
  sorry

/-- The transported generic modulus has positive degree. -/
theorem fpModulus_degree_pos (hirr : GF2Poly.Irreducible f) :
    0 < (fpModulus f).degree := by
  let _ := hirr
  sorry

/--
The generic quotient-field carrier corresponding to the packed multi-word
extension `GF2nPoly f hirr`.
-/
abbrev FieldCarrier (f : GF2Poly) (hirr : GF2Poly.Irreducible f) :=
  HexGfqField.FiniteField 2 (fpModulus f) (fpModulus_degree_pos hirr)
    (fpModulus_irreducible hirr)

/-- Convert a packed `GF2nPoly` element into the generic quotient-field carrier. -/
def toFieldCarrier (x : GF2nPoly f hirr) : FieldCarrier f hirr :=
  HexGfqField.ofPoly (f := fpModulus f) (hirr := fpModulus_irreducible hirr)
    (fpModulus_degree_pos hirr) (GF2Poly.toFpPoly (toPoly x))

/-- Convert the generic quotient-field carrier back into the packed `GF2nPoly` form. -/
def ofFieldCarrier (x : FieldCarrier f hirr) : GF2nPoly f hirr :=
  ofPoly (f := f) (GF2Poly.ofFpPoly (HexGfqField.repr x)) hirr

/-- Converting to the generic quotient-field wrapper exposes the packed representative. -/
theorem toFieldCarrier_repr (x : GF2nPoly f hirr) :
    HexGfqField.repr (toFieldCarrier x) = HexGfqRing.reduceMod (fpModulus f) (GF2Poly.toFpPoly x.val) := by
  rfl

/-- Converting back from the generic quotient-field wrapper repacks its canonical representative. -/
theorem toPoly_ofFieldCarrier (x : FieldCarrier f hirr) :
    toPoly (ofFieldCarrier x) = reduce (GF2Poly.ofFpPoly (HexGfqField.repr x)) f := by
  rfl

/-- Packed and generic multi-word `GF(2^n)` carriers are ring-equivalent. -/
noncomputable def fieldEquiv : GF2nPoly f hirr ≃+* FieldCarrier f hirr where
  toFun := toFieldCarrier
  invFun := ofFieldCarrier
  left_inv := by
    intro x
    sorry
  right_inv := by
    intro x
    sorry
  map_mul' := by
    intro x y
    sorry
  map_add' := by
    intro x y
    sorry

end GF2nPoly

end HexGF2
