import HexGF2
import HexPolyFp

/-!
Bridge definitions between packed `Hex.GF2Poly` values and the generic
`Hex.FpPoly 2` representation.

This Phase 1 module exposes the concrete unpack/repack conversions between the
bit-packed `GF(2)` polynomial execution path and the generic dense polynomial
over `Hex.ZMod64 2`, together with the ring equivalence and immediate simp
lemmas needed by later `GF(2^n)` bridge modules.
-/

namespace HexGF2Mathlib

open Hex

universe u v

/-! A minimal project-local ring equivalence structure for executable algebra
types that have not imported Mathlib's heavier equivalence hierarchy. -/
structure RingEquiv (R : Type u) (S : Type v) [Mul R] [Mul S] [Add R] [Add S] where
  toFun : R → S
  invFun : S → R
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
  map_mul' : ∀ a b : R, toFun (a * b) = toFun a * toFun b
  map_add' : ∀ a b : R, toFun (a + b) = toFun a + toFun b

infixl:25 " ≃+* " => RingEquiv

namespace RingEquiv

variable {R : Type u} {S : Type v} [Mul R] [Mul S] [Add R] [Add S]

instance : CoeFun (R ≃+* S) (fun _ => R → S) where
  coe e := e.toFun

/-- The inverse of a project-local ring equivalence. -/
def symm (e : R ≃+* S) : S ≃+* R where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_mul' := by
    intro a b
    sorry
  map_add' := by
    intro a b
    sorry

end RingEquiv

namespace GF2Poly

instance : Hex.ZMod64.Bounds 2 := ⟨by decide, by decide⟩

/-- Interpret a packed `GF2Poly` coefficient as the corresponding `ZMod64 2`
residue. -/
private def coeffToFp (b : Bool) : Hex.ZMod64 2 :=
  if b then Hex.ZMod64.one else Hex.ZMod64.zero

/-- Pack a `ZMod64 2` coefficient into a single bit. -/
private def coeffOfFp (a : Hex.ZMod64 2) : UInt64 :=
  if a = Hex.ZMod64.zero then 0 else 1

/-- Unpack a packed `GF2Poly` into the generic dense polynomial over
`Hex.ZMod64 2`. -/
def toFpPoly (p : Hex.GF2Poly) : Hex.FpPoly 2 :=
  let coeffs :=
    if p.isZero then
      #[]
    else
      ((List.range (p.degree + 1)).map fun i => coeffToFp (p.coeff i)).toArray
  Hex.FpPoly.ofCoeffs coeffs

/-- Pack the coefficients of a single 64-term `FpPoly 2` segment into one
machine word. -/
private def packWord (p : Hex.FpPoly 2) (wordIdx : Nat) : UInt64 :=
  (List.range 64).foldl
    (fun acc bitIdx =>
      let coeff := p.coeff (64 * wordIdx + bitIdx)
      let bit := coeffOfFp coeff <<< bitIdx.toUInt64
      acc ||| bit)
    0

/-- Repack a generic dense polynomial over `Hex.ZMod64 2` into the packed
`GF2Poly` representation. -/
def ofFpPoly (p : Hex.FpPoly 2) : Hex.GF2Poly :=
  let wordCount := (p.size + 63) / 64
  let words := Array.ofFn fun i : Fin wordCount => packWord p i.1
  Hex.GF2Poly.ofWords words

@[simp]
theorem toFpPoly_zero :
    toFpPoly (0 : Hex.GF2Poly) = 0 := by
  rfl

@[simp]
theorem ofFpPoly_zero :
    ofFpPoly (0 : Hex.FpPoly 2) = 0 := by
  rfl

@[simp]
theorem toFpPoly_one :
    toFpPoly (1 : Hex.GF2Poly) = 1 := by
  sorry

@[simp]
theorem ofFpPoly_toFpPoly (p : Hex.GF2Poly) :
    ofFpPoly (toFpPoly p) = p := by
  sorry

@[simp]
theorem toFpPoly_ofFpPoly (p : Hex.FpPoly 2) :
    toFpPoly (ofFpPoly p) = p := by
  sorry

@[simp]
theorem toFpPoly_add (p q : Hex.GF2Poly) :
    toFpPoly (p + q) = toFpPoly p + toFpPoly q := by
  sorry

@[simp]
theorem toFpPoly_mul (p q : Hex.GF2Poly) :
    toFpPoly (p * q) = toFpPoly p * toFpPoly q := by
  sorry

/-- The packed `GF2Poly` representation is ring-equivalent to the generic
degree-normalized `FpPoly 2` representation. -/
def equiv : Hex.GF2Poly ≃+* Hex.FpPoly 2 where
  toFun := toFpPoly
  invFun := ofFpPoly
  left_inv := ofFpPoly_toFpPoly
  right_inv := toFpPoly_ofFpPoly
  map_mul' := toFpPoly_mul
  map_add' := toFpPoly_add

@[simp]
theorem equiv_apply (p : Hex.GF2Poly) :
    equiv p = toFpPoly p := by
  rfl

@[simp]
theorem equiv_symm_apply (p : Hex.FpPoly 2) :
    RingEquiv.symm equiv p = ofFpPoly p := by
  rfl

end GF2Poly

end HexGF2Mathlib
