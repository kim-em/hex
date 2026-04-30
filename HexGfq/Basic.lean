import HexConway
import HexGF2
import HexGfqField

/-!
User-facing canonical finite-field constructors.

This module packages committed Conway-table entries as generic quotient-field
types.  The generic `GFq` constructor always uses the `HexGfqField` quotient
representation; optimized packed characteristic-two constructors are kept to
separate declarations so the representation choice remains explicit.
-/
namespace Hex

namespace Conway

/-- Interpret a packed single-word binary modulus as the corresponding generic
`FpPoly 2` polynomial.  `lower` supplies the coefficients of degrees `< n`;
the leading degree-`n` coefficient is inserted explicitly. -/
def packedGF2FpPoly (lower : UInt64) (n : Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs <|
    (((List.range n).map fun i =>
      if (((lower >>> i.toUInt64) &&& 1) = 0) then
        (0 : ZMod64 2)
      else
        (1 : ZMod64 2)).toArray).push 1

/-- A committed Conway-table entry at `p = 2` that is also available as a
single-word packed `GF2n` modulus.  The `lower` field stores the lower
coefficients of the monic degree-`n` modulus; the leading `x^n` coefficient is
implicit in `GF2Poly.ofUInt64Monic lower n`. -/
class PackedGF2Entry (n : Nat) where
  entry : SupportedEntry 2 n
  lower : UInt64
  conway_eq_packed : conwayPoly 2 n entry = packedGF2FpPoly lower n
  degree_pos : 0 < n
  degree_lt_word : n < 64
  packed_irreducible : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n)

/-- The packed modulus corresponding to the committed Conway entry `C(2, 1) =
X + 1`. -/
theorem packedGF2Entry_2_1_irreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 1 1) := by
  sorry

/-- The current committed table supports a packed `GF2n` view of `C(2, 1)`. -/
instance packedGF2Entry_2_1 : PackedGF2Entry 1 where
  entry := supportedEntry_2_1
  lower := 1
  conway_eq_packed := rfl
  degree_pos := by decide
  degree_lt_word := by decide
  packed_irreducible := packedGF2Entry_2_1_irreducible

end Conway

/-- Canonical finite field with `p^n` elements for a committed Conway-table
entry, using the generic quotient-field representation. -/
abbrev GFq (p n : Nat) [ZMod64.Bounds p] (h : Conway.SupportedEntry p n) : Type :=
  GFqField.FiniteField (Conway.conwayPoly p n h)
    (Conway.conwayPoly_nonconstant p n h)
    (Conway.conwayPoly_irreducible p n h)

namespace GFq

variable {p n : Nat} [ZMod64.Bounds p]

/-- The Conway modulus selected for a committed `GFq p n` entry. -/
abbrev modulus (h : Conway.SupportedEntry p n) : FpPoly p :=
  Conway.conwayPoly p n h

/-- The selected Conway modulus has positive degree. -/
theorem modulus_nonconstant (h : Conway.SupportedEntry p n) :
    0 < FpPoly.degree (modulus h) :=
  Conway.conwayPoly_nonconstant p n h

/-- The selected Conway modulus is irreducible. -/
theorem modulus_irreducible (h : Conway.SupportedEntry p n) :
    FpPoly.Irreducible (modulus h) :=
  Conway.conwayPoly_irreducible p n h

/-- Reduce a polynomial into the canonical field selected by a committed Conway
entry. -/
def ofPoly (h : Conway.SupportedEntry p n) (g : FpPoly p) : GFq p n h :=
  GFqField.ofPoly (modulus h) (modulus_nonconstant h) (modulus_irreducible h) g

/-- Project a canonical field element to its reduced polynomial representative. -/
def repr {h : Conway.SupportedEntry p n} (x : GFq p n h) : FpPoly p :=
  GFqField.repr x

@[simp] theorem repr_ofPoly (h : Conway.SupportedEntry p n) (g : FpPoly p) :
    repr (ofPoly h g) = GFqRing.reduceMod (modulus h) g :=
  rfl

end GFq

/-- Optimized canonical binary field for committed Conway entries that have a
single-word packed modulus. -/
abbrev GF2q (n : Nat) [h : Conway.PackedGF2Entry n] : Type :=
  GF2n n h.lower h.degree_pos h.degree_lt_word h.packed_irreducible

namespace GF2q

variable {n : Nat} [h : Conway.PackedGF2Entry n]

/-- The supported Conway-table entry backing this optimized binary field. -/
def supportedEntry : Conway.SupportedEntry 2 n :=
  h.entry

/-- The lower-word packed modulus selected for a committed optimized `GF2q`
entry. -/
def lower : UInt64 :=
  h.lower

/-- The packed modulus polynomial selected for a committed optimized `GF2q`
entry. -/
def modulus : GF2Poly :=
  GF2Poly.ofUInt64Monic h.lower n

/-- The packed modulus, viewed through the generic `FpPoly 2` representation,
is the committed Conway polynomial for this entry. -/
theorem conway_eq_packed :
    Conway.conwayPoly 2 n h.entry = Conway.packedGF2FpPoly h.lower n :=
  h.conway_eq_packed

/-- The selected packed modulus has positive extension degree. -/
theorem degree_pos : 0 < n :=
  h.degree_pos

/-- The selected packed modulus fits in the single-word `GF2n` representation. -/
theorem degree_lt_word : n < 64 :=
  h.degree_lt_word

/-- The selected packed modulus is irreducible. -/
theorem modulus_irreducible : GF2Poly.Irreducible (modulus (n := n)) :=
  h.packed_irreducible

/-- Reduce a machine word into the optimized binary field selected by a
committed packed Conway entry. -/
def ofWord (w : UInt64) : GF2q n :=
  GF2n.reduce (n := n) (irr := h.lower) w

/-- Project an optimized binary field element to its packed machine-word
representative. -/
def repr (x : GF2q n) : UInt64 :=
  x.val

@[simp] theorem repr_ofWord (w : UInt64) :
    repr (ofWord (n := n) w) =
      (GF2n.reduce
        (n := n) (irr := h.lower)
        (hn := h.degree_pos) (hn64 := h.degree_lt_word)
        (hirr := h.packed_irreducible) w).val :=
  rfl

end GF2q

end Hex
