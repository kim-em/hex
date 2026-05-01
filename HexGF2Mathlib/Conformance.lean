import HexGF2Mathlib.Field

/-!
Core conformance checks for `HexGF2Mathlib`.

Oracle:
- none for this `core` profile; checks are deterministic Lean-side bridge
  fixtures.

Mode:
- always.

Covered operations:
- `GF2Poly.toFpPoly` and `GF2Poly.ofFpPoly`.
- `GF2Poly.equiv` and its project-local inverse.
- `GF2n.equiv`, `GF2n.finEquiv`, and `GF2n.fintype_card`.
- `GF2nPoly.equiv`, `GF2nPoly.finEquiv`, and `GF2nPoly.fintype_card`.

Covered properties:
- packed-polynomial conversion round trips preserve coefficients on committed
  zero, typical, and cross-word inputs.
- the packed-polynomial ring equivalence agrees with the named conversion
  functions and transports addition/multiplication on committed inputs.
- finite-index surfaces expose the canonical packed representatives and the
  cardinality formulas for small committed single-word and packed-polynomial
  `GF(2^n)` instances.

Covered edge cases:
- zero packed polynomials and zero dense polynomials.
- trailing-zero dense coefficients.
- coefficients crossing the 63/64 word boundary.
- zero and one finite-field elements.
- AES-style degree-eight irreducible modulus fixtures.
-/

namespace HexGF2Mathlib

open Hex

namespace GF2Poly

private instance conformanceBoundsTwo : Hex.ZMod64.Bounds 2 := ⟨by decide, by decide⟩

private def polyTwo (coeffs : Array Nat) : Hex.FpPoly 2 :=
  Hex.FpPoly.ofCoeffs (coeffs.map (fun n => Hex.ZMod64.ofNat 2 n))

private def coeffNats (f : Hex.FpPoly 2) : List Nat :=
  f.toArray.toList.map Hex.ZMod64.toNat

private def words (p : Hex.GF2Poly) : Array UInt64 :=
  p.toWords

private def packedTypical : Hex.GF2Poly :=
  Hex.GF2Poly.ofUInt64 0b1011

private def packedCrossWord : Hex.GF2Poly :=
  Hex.GF2Poly.monomial 63 + Hex.GF2Poly.monomial 64 + Hex.GF2Poly.monomial 70

private def denseTypical : Hex.FpPoly 2 :=
  polyTwo #[1, 1, 0, 1]

private def denseTrailingZeros : Hex.FpPoly 2 :=
  polyTwo #[1, 0, 1, 0, 0]

private def denseCrossWord : Hex.FpPoly 2 :=
  polyTwo ((Array.replicate 63 0).push 1 |>.push 1 |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 0 |>.push 1)

#guard coeffNats (toFpPoly (0 : Hex.GF2Poly)) = []
#guard coeffNats (toFpPoly packedTypical) = [1, 1, 0, 1]
#guard (toFpPoly packedCrossWord).coeff 63 = 1
#guard (toFpPoly packedCrossWord).coeff 64 = 1
#guard (toFpPoly packedCrossWord).coeff 70 = 1

#guard words (ofFpPoly (0 : Hex.FpPoly 2)) = #[]
#guard words (ofFpPoly denseTypical) = #[0b1011]
#guard words (ofFpPoly denseTrailingZeros) = #[0b101]
#guard words (ofFpPoly denseCrossWord) = #[((1 : UInt64) <<< 63), 0x41]

#guard words (ofFpPoly (toFpPoly (0 : Hex.GF2Poly))) = #[]
#guard words (ofFpPoly (toFpPoly packedTypical)) = words packedTypical
#guard words (ofFpPoly (toFpPoly packedCrossWord)) = words packedCrossWord

#guard coeffNats (toFpPoly (ofFpPoly (0 : Hex.FpPoly 2))) = []
#guard coeffNats (toFpPoly (ofFpPoly denseTypical)) = coeffNats denseTypical
#guard coeffNats (toFpPoly (ofFpPoly denseCrossWord)) = coeffNats denseCrossWord

#guard equiv (0 : Hex.GF2Poly) = toFpPoly 0
#guard equiv packedTypical = toFpPoly packedTypical
#guard equiv packedCrossWord = toFpPoly packedCrossWord

#guard words (RingEquiv.symm equiv (0 : Hex.FpPoly 2)) = #[]
#guard words (RingEquiv.symm equiv denseTypical) = words packedTypical
#guard words (RingEquiv.symm equiv denseCrossWord) = words packedCrossWord

#guard equiv (packedTypical + packedCrossWord) = equiv packedTypical + equiv packedCrossWord
#guard equiv (packedTypical * Hex.GF2Poly.monomial 2) =
  equiv packedTypical * equiv (Hex.GF2Poly.monomial 2)

end GF2Poly

private theorem aesIrreducible :
    Hex.GF2Poly.Irreducible (Hex.GF2Poly.ofUInt64Monic 0x1B 8) := by
  sorry

namespace GF2n

private abbrev AESField : Type :=
  Hex.GF2n 8 0x1B (by decide) (by decide) aesIrreducible

private def aes (word : UInt64) : AESField :=
  Hex.GF2n.reduce word

#guard (finEquiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
    (hirr := aesIrreducible) (aes 0)).1 = 0
#guard (finEquiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
    (hirr := aesIrreducible) (aes 1)).1 = 1
#guard (finEquiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
    (hirr := aesIrreducible) (aes 0xCA)).1 = 0xCA

#guard (2 ^ 8 : Nat) = 256

example :
    Fintype.card AESField = 2 ^ 8 :=
  fintype_card (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
    (hirr := aesIrreducible)

example :
    equiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
    (hirr := aesIrreducible) (aes 0) =
      toGeneric (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
        (hirr := aesIrreducible) (aes 0) := by
  rfl

example :
    RingEquiv.symm
    (equiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
      (hirr := aesIrreducible))
    (toGeneric (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
      (hirr := aesIrreducible) (aes 1)) = aes 1 := by
  exact RingEquiv.left_inv
    (equiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
      (hirr := aesIrreducible))
    (aes 1)

example :
    equiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
    (hirr := aesIrreducible) (aes 0x53 + aes 0xCA) =
      equiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
        (hirr := aesIrreducible) (aes 0x53) +
      equiv (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
        (hirr := aesIrreducible) (aes 0xCA) := by
  exact toGeneric_add (n := 8) (irr := 0x1B) (hn := by decide) (hn64 := by decide)
    (hirr := aesIrreducible)
    (aes 0x53)
    (aes 0xCA)

end GF2n

namespace GF2nPoly

private def aesModulus : Hex.GF2Poly :=
  Hex.GF2Poly.ofUInt64Monic 0x1B 8

private abbrev AESPolyField : Type :=
  Hex.GF2nPoly aesModulus aesIrreducible

private def aesPoly (word : UInt64) : AESPolyField :=
  Hex.GF2nPoly.reducePoly (f := aesModulus) (Hex.GF2Poly.ofUInt64 word)

#guard (finEquiv (f := aesModulus) (hirr := aesIrreducible) (aesPoly 0)).1 = 0
#guard (finEquiv (f := aesModulus) (hirr := aesIrreducible) (aesPoly 1)).1 = 1
#guard (finEquiv (f := aesModulus) (hirr := aesIrreducible) (aesPoly 0xCA)).1 = 0xCA

#guard (2 ^ aesModulus.degree : Nat) = 256

example :
    Fintype.card AESPolyField = 2 ^ aesModulus.degree :=
  fintype_card (f := aesModulus) (hirr := aesIrreducible)

example :
    equiv (f := aesModulus) (hirr := aesIrreducible) (aesPoly 0) =
      toGeneric (f := aesModulus) (hirr := aesIrreducible) (aesPoly 0) := by
  rfl

example :
    RingEquiv.symm (equiv (f := aesModulus) (hirr := aesIrreducible))
      (toGeneric (f := aesModulus) (hirr := aesIrreducible) (aesPoly 1)) =
        aesPoly 1 := by
  exact RingEquiv.left_inv (equiv (f := aesModulus) (hirr := aesIrreducible))
    (aesPoly 1)

example :
    equiv (f := aesModulus) (hirr := aesIrreducible) (aesPoly 0x53 * aesPoly 0xCA) =
      equiv (f := aesModulus) (hirr := aesIrreducible) (aesPoly 0x53) *
      equiv (f := aesModulus) (hirr := aesIrreducible) (aesPoly 0xCA) := by
  exact toGeneric_mul (f := aesModulus) (hirr := aesIrreducible)
    (aesPoly 0x53)
    (aesPoly 0xCA)

end GF2nPoly

end HexGF2Mathlib
