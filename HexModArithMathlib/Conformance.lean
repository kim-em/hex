import HexModArithMathlib.Basic

/-!
Core conformance checks for `hex-mod-arith-mathlib`.

Oracle: none
Mode: always
Covered operations:
- `ZMod64.toZMod`
- `ZMod64.ofZMod`
- `ZMod64.ofZMod_toZMod`
- `ZMod64.toZMod_ofZMod`
- `ZMod64.equiv`
Covered properties:
- executable residues convert to Mathlib `ZMod` with the same canonical representative
- Mathlib `ZMod` residues convert back to executable residues with the same canonical representative
- converting executable residues to Mathlib and back is the identity
- converting Mathlib residues to executable residues and back is the identity
- the ring equivalence agrees with the forward and inverse conversion functions
Covered edge cases:
- modulus `1`
- small prime modulus `7`
- large word-sized modulus `2^63 + 29`
- non-canonical natural representatives
-/

namespace HexModArithMathlib
namespace ZMod64

private abbrev LargeMod : Nat := 2 ^ 63 + 29

private instance conformanceBoundsOne : Hex.ZMod64.Bounds 1 := ⟨by decide, by decide⟩
private instance conformanceBoundsSeven : Hex.ZMod64.Bounds 7 := ⟨by decide, by decide⟩
private instance conformanceBoundsLarge : Hex.ZMod64.Bounds LargeMod := ⟨by decide, by decide⟩

private def primeResidue : Hex.ZMod64 7 := Hex.ZMod64.ofNat 7 5
private def oneResidue : Hex.ZMod64 1 := Hex.ZMod64.ofNat 1 37
private def largeResidue : Hex.ZMod64 LargeMod := Hex.ZMod64.ofNat LargeMod (LargeMod + 123)

#guard (toZMod primeResidue).val = primeResidue.toNat
#guard (toZMod oneResidue).val = oneResidue.toNat
#guard (toZMod largeResidue).val = largeResidue.toNat

#guard (ofZMod ((19 : Nat) : ZMod 7)).toNat = 19 % 7
#guard (ofZMod ((37 : Nat) : ZMod 1)).toNat = 37 % 1
#guard (ofZMod ((LargeMod + 123 : Nat) : ZMod LargeMod)).toNat =
  (LargeMod + 123) % LargeMod

example : ofZMod (toZMod primeResidue) = primeResidue :=
  ofZMod_toZMod primeResidue

example : ofZMod (toZMod oneResidue) = oneResidue :=
  ofZMod_toZMod oneResidue

example : ofZMod (toZMod largeResidue) = largeResidue :=
  ofZMod_toZMod largeResidue

example : toZMod (ofZMod ((19 : Nat) : ZMod 7)) = ((19 : Nat) : ZMod 7) :=
  toZMod_ofZMod ((19 : Nat) : ZMod 7)

example : toZMod (ofZMod ((37 : Nat) : ZMod 1)) = ((37 : Nat) : ZMod 1) :=
  toZMod_ofZMod ((37 : Nat) : ZMod 1)

example :
    toZMod (ofZMod ((LargeMod + 123 : Nat) : ZMod LargeMod)) =
      ((LargeMod + 123 : Nat) : ZMod LargeMod) :=
  toZMod_ofZMod ((LargeMod + 123 : Nat) : ZMod LargeMod)

#guard ((equiv : Hex.ZMod64 7 ≃+* ZMod 7) primeResidue).val = primeResidue.toNat
#guard ((equiv : Hex.ZMod64 1 ≃+* ZMod 1) oneResidue).val = oneResidue.toNat
#guard ((equiv : Hex.ZMod64 LargeMod ≃+* ZMod LargeMod) largeResidue).val =
  largeResidue.toNat

#guard (((equiv : Hex.ZMod64 7 ≃+* ZMod 7).symm ((19 : Nat) : ZMod 7)).toNat) =
  19 % 7
#guard (((equiv : Hex.ZMod64 1 ≃+* ZMod 1).symm ((37 : Nat) : ZMod 1)).toNat) =
  37 % 1
#guard (((equiv : Hex.ZMod64 LargeMod ≃+* ZMod LargeMod).symm
    ((LargeMod + 123 : Nat) : ZMod LargeMod)).toNat) =
  (LargeMod + 123) % LargeMod

end ZMod64
end HexModArithMathlib
