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

end Hex
