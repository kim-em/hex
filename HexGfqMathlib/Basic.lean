import HexGfq
import HexGF2Mathlib.Field
import Mathlib.FieldTheory.Finite.GaloisField

/-!
Generic Mathlib-side scaffolding for the executable `GFq` model.

This module exposes the concrete reduced-representative enumeration used to
transport `Fintype` support onto generic `Hex.GFqField.FiniteField` values, and
states the canonical-cardinality bridge to Mathlib's `GaloisField`.
-/

namespace HexGfqMathlib

open Hex

namespace FpPoly

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Interpret the first `degree` coefficients of an `FpPoly` as a base-`p`
index. -/
def coeffIndex (degree : Nat) (f : Hex.FpPoly p) : Nat :=
  (List.range degree).foldl
    (fun acc i => acc + (f.coeff i).toNat * p ^ i)
    0

/-- Decode a base-`p` index into a polynomial with at most `degree`
coefficients. -/
def ofIndexBelowDegree (degree index : Nat) : Hex.FpPoly p :=
  Hex.FpPoly.ofCoeffs <|
    ((List.range degree).map fun i =>
      Hex.ZMod64.ofNat p (index / p ^ i)).toArray

/-- Bounded reduced polynomials encode to indices below `p ^ degree`. -/
theorem coeffIndex_lt_of_degree_lt {degree : Nat} {f : Hex.FpPoly p}
    (_hdeg : Hex.FpPoly.degree f < degree) :
    coeffIndex degree f < p ^ degree := by
  sorry

/-- Decoded indices are represented by polynomials with degree below the
requested bound. -/
theorem ofIndexBelowDegree_degree_lt (degree : Nat) (index : Fin (p ^ degree)) :
    Hex.FpPoly.degree (ofIndexBelowDegree (p := p) degree index.1) < degree := by
  sorry

/-- Encoding after decoding recovers the bounded index. -/
@[simp]
theorem coeffIndex_ofIndexBelowDegree (degree : Nat) (index : Fin (p ^ degree)) :
    coeffIndex degree (ofIndexBelowDegree (p := p) degree index.1) = index.1 := by
  sorry

/-- Decoding after encoding recovers a polynomial already below the degree
bound. -/
@[simp]
theorem ofIndexBelowDegree_coeffIndex {degree : Nat} {f : Hex.FpPoly p}
    (hdeg : Hex.FpPoly.degree f < degree) :
    ofIndexBelowDegree (p := p) degree (coeffIndex degree f) = f := by
  sorry

end FpPoly

namespace FiniteField

variable {p : Nat} [Hex.ZMod64.Bounds p]
variable {f : Hex.FpPoly p}
variable {hf : 0 < Hex.FpPoly.degree f}
variable {hp : Hex.Nat.Prime p}
variable {hirr : Hex.FpPoly.Irreducible f}

/-- Reduced polynomial representatives for the quotient by `f`. -/
abbrev ReducedRep (f : Hex.FpPoly p) : Type :=
  { g : Hex.FpPoly p // Hex.FpPoly.degree g < Hex.FpPoly.degree f }

/-- The executable finite-field wrapper is equivalent to its canonical reduced
polynomial representatives. -/
def reducedRepEquiv :
    HexGF2Mathlib.TypeEquiv
      (Hex.GFqField.FiniteField f hf hp hirr)
      (ReducedRep f) where
  toFun x := ⟨Hex.GFqField.repr x, Hex.GFqField.degree_repr_lt_degree x⟩
  invFun x := Hex.GFqField.ofPoly f hf hp hirr x.1
  left_inv := by
    intro x
    sorry
  right_inv := by
    intro x
    sorry

/-- Reduced representatives are indexed by `Fin (p ^ degree f)`. -/
def reducedRepFinEquiv (f : Hex.FpPoly p) :
    HexGF2Mathlib.TypeEquiv
      (ReducedRep f)
      (Fin (p ^ Hex.FpPoly.degree f)) where
  toFun x :=
    ⟨FpPoly.coeffIndex (Hex.FpPoly.degree f) x.1,
      FpPoly.coeffIndex_lt_of_degree_lt x.2⟩
  invFun index :=
    ⟨FpPoly.ofIndexBelowDegree (p := p) (Hex.FpPoly.degree f) index.1,
      FpPoly.ofIndexBelowDegree_degree_lt (p := p) (Hex.FpPoly.degree f) index⟩
  left_inv := by
    intro x
    exact Subtype.ext (FpPoly.ofIndexBelowDegree_coeffIndex x.2)
  right_inv := by
    intro index
    exact Fin.ext (FpPoly.coeffIndex_ofIndexBelowDegree (p := p)
      (Hex.FpPoly.degree f) index)

/-- Generic finite-field elements are equivalent to the expected finite index
type. -/
noncomputable def finEquiv :
    Hex.GFqField.FiniteField f hf hp hirr ≃
      Fin (p ^ Hex.FpPoly.degree f) :=
  HexGF2Mathlib.TypeEquiv.toEquiv <|
    HexGF2Mathlib.TypeEquiv.trans reducedRepEquiv (reducedRepFinEquiv f)

/-- The generic executable finite-field wrapper is finite. -/
noncomputable instance fintype :
    Fintype (Hex.GFqField.FiniteField f hf hp hirr) :=
  Fintype.ofEquiv (Fin (p ^ Hex.FpPoly.degree f)) finEquiv.symm

/-- The generic executable finite-field wrapper has the expected cardinality. -/
theorem fintype_card :
    Fintype.card (Hex.GFqField.FiniteField f hf hp hirr) =
      p ^ Hex.FpPoly.degree f := by
  simpa using Fintype.card_congr (finEquiv (f := f) (hf := hf)
    (hp := hp) (hirr := hirr))

end FiniteField

namespace GFq

variable {p n : Nat} [Hex.ZMod64.Bounds p]

/-- Canonical Conway-backed `GFq` values inherit the generic finite-field
enumeration. -/
noncomputable instance fintype (h : Hex.Conway.SupportedEntry p n) :
    Fintype (Hex.GFq p n h) :=
  FiniteField.fintype

/-- Cardinality of the canonical Conway-backed `GFq` in terms of its selected
modulus degree. -/
theorem fintype_card (h : Hex.Conway.SupportedEntry p n) :
    Fintype.card (Hex.GFq p n h) =
      p ^ Hex.FpPoly.degree (Hex.GFq.modulus h) := by
  simpa [Hex.GFq, Hex.GFq.modulus] using
    (FiniteField.fintype_card
      (f := Hex.GFq.modulus h)
      (hf := Hex.GFq.modulus_nonconstant h)
      (hp := Hex.GFq.modulus_prime h)
      (hirr := Hex.GFq.modulus_irreducible h))

/-- The committed Conway modulus has the requested extension degree. -/
theorem modulus_degree (h : Hex.Conway.SupportedEntry p n) :
    Hex.FpPoly.degree (Hex.GFq.modulus h) = n := by
  sorry

/-- Cardinality of canonical `GFq p n` as `p ^ n`. -/
theorem fintype_card_eq_pow (h : Hex.Conway.SupportedEntry p n) :
    Fintype.card (Hex.GFq p n h) = p ^ n := by
  rw [fintype_card h, modulus_degree h]

/-- Canonical `GFq` and Mathlib's `GaloisField` have matching cardinalities. -/
theorem card_eq_galoisField_card [Fact p.Prime]
    (h : Hex.Conway.SupportedEntry p n) (hn : n ≠ 0) :
    Fintype.card (Hex.GFq p n h) = Nat.card (GaloisField p n) := by
  rw [fintype_card_eq_pow h, GaloisField.card p n hn]

end GFq

end HexGfqMathlib
