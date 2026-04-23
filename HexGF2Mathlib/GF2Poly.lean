import Mathlib.Algebra.Ring.Equiv
import HexGF2
import HexPolyFp

/-!
Mathlib bridge scaffolding for packed `GF(2)` polynomials.

This module introduces explicit conversion functions between the packed
bit-vector representation `HexGF2.GF2Poly` and the generic executable
polynomial type `HexPolyFp.FpPoly 2`, together with the scaffolded ring
equivalence that downstream finite-field bridges will transport across.
-/

namespace HexGF2

namespace GF2Poly

open HexModArith

/-- Interpret a packed bit as the corresponding coefficient of `FpPoly 2`. -/
private def coeffOfBit (word : UInt64) (bit : Nat) : ZMod64 2 :=
  if word &&& ((1 : UInt64) <<< UInt64.ofNat bit) = 0 then 0 else 1

/--
Expand a packed `GF2Poly` into low-to-high coefficients over `ZMod64 2`.

The zero polynomial contributes only zero coefficients, so normalization on
the `FpPoly` side drops the trailing zero scaffold automatically.
-/
def toFpPolyCoeffs (f : GF2Poly) : Array (ZMod64 2) := Id.run do
  let mut coeffs : Array (ZMod64 2) := #[]
  for i in List.range (f.degree + 1) do
    let word := f.words.getD (i / 64) 0
    coeffs := coeffs.push (coeffOfBit word (i % 64))
  pure coeffs

/-- Convert a packed `GF(2)` polynomial into the generic `FpPoly 2` form. -/
def toFpPoly (f : GF2Poly) : HexPolyFp.FpPoly 2 :=
  HexPolyFp.FpPoly.ofCoeffs (toFpPolyCoeffs f)

/-- Number of 64-bit words needed to store a coefficient array. -/
private def wordCount (coeffs : Array (ZMod64 2)) : Nat :=
  if coeffs.isEmpty then 0 else (coeffs.size - 1) / 64 + 1

/-- Set the target bit when a coefficient of `FpPoly 2` is nonzero. -/
private def setCoeffBit (words : Array UInt64) (i : Nat) (coeff : ZMod64 2) :
    Array UInt64 :=
  if coeff.toNat = 0 then
    words
  else
    let wordIdx := i / 64
    let mask := (1 : UInt64) <<< UInt64.ofNat (i % 64)
    words.set! wordIdx (words[wordIdx]! ||| mask)

/-- Pack low-to-high `FpPoly 2` coefficients back into `GF2Poly` words. -/
def ofFpPolyWords (f : HexPolyFp.FpPoly 2) : Array UInt64 := Id.run do
  let coeffs := f.coeffs
  let mut words : Array UInt64 := (List.replicate (wordCount coeffs) (0 : UInt64)).toArray
  for i in List.range coeffs.size do
    words := setCoeffBit words i coeffs[i]!
  pure words

/-- Convert the generic `FpPoly 2` representation into packed `GF2Poly`. -/
def ofFpPoly (f : HexPolyFp.FpPoly 2) : GF2Poly :=
  ofWords (ofFpPolyWords f)

/-- Packing after unpacking recovers the original packed polynomial. -/
@[simp] theorem ofFpPoly_toFpPoly (f : GF2Poly) :
    ofFpPoly (toFpPoly f) = f := by
  sorry

/-- Unpacking after packing recovers the original generic `FpPoly 2`. -/
@[simp] theorem toFpPoly_ofFpPoly (f : HexPolyFp.FpPoly 2) :
    toFpPoly (ofFpPoly f) = f := by
  sorry

/-- Packed and generic executable `GF(2)` polynomials are ring-equivalent. -/
def fpPolyEquiv : GF2Poly ≃+* HexPolyFp.FpPoly 2 where
  toFun := toFpPoly
  invFun := ofFpPoly
  left_inv := ofFpPoly_toFpPoly
  right_inv := toFpPoly_ofFpPoly
  map_mul' := by
    intro f g
    sorry
  map_add' := by
    intro f g
    sorry

end GF2Poly

end HexGF2
