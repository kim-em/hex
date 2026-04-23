import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.OfMap
import HexGF2.GF2n

/-!
Mathlib bridge scaffolding for the small-word `GF2n` carrier.

This module adds the `Fintype` and `Field` instances promised by the
Phase 1 spec on top of the executable arithmetic defined in `HexGF2.GF2n`.
-/

namespace HexGF2

namespace GF2n

/-- Canonical equivalence between packed representatives and `Fin (2^n)`. -/
def finEquiv {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    GF2n n irr hn hn64 hirr ≃ Fin (2 ^ n) where
  toFun x := ⟨x.val.toNat, x.val_lt⟩
  invFun k := ofUInt64 (n := n) (irr := irr) (hn := hn) (hn64 := hn64)
    (hirr := hirr) (UInt64.ofNat k.1)
  left_inv x := by
    apply ext
    sorry
  right_inv k := by
    apply Fin.ext
    sorry

/-- The small-word carrier is finite by enumeration of its `n`-bit representatives. -/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Fintype (GF2n n irr hn hn64 hirr) :=
  Fintype.ofEquiv (Fin (2 ^ n)) (finEquiv (n := n) (irr := irr) (hn := hn)
    (hn64 := hn64) (hirr := hirr)).symm

/-- The finite enumeration is definitionally the `Fin` enumeration transported across `finEquiv`. -/
theorem fintype_card {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Fintype.card (GF2n n irr hn hn64 hirr) = 2 ^ n := by
  sorry

/-- The small-word carrier supports the spec-promised field structure. -/
noncomputable instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Field (GF2n n irr hn hn64 hirr) :=
  Field.ofMinimalAxioms (GF2n n irr hn hn64 hirr)
    (fun a b c => by sorry)
    (fun a => by sorry)
    (fun a => by sorry)
    (fun a b c => by sorry)
    (fun a b => by sorry)
    (fun a => by sorry)
    (fun a ha => by
      simpa [Inv.inv, inv] using mul_inv_cancel (n := n) (irr := irr) (hn := hn)
        (hn64 := hn64) (hirr := hirr) a ha)
    (by
      exact inv_zero (n := n) (irr := irr) (hn := hn)
        (hn64 := hn64) (hirr := hirr))
    (fun a b c => by sorry)
    (by
      refine ⟨0, 1, ?_⟩
      intro h
      have := congrArg GF2n.val h
      simp [zero_val, one_val] at this)

end GF2n

end HexGF2
