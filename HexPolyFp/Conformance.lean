import HexPolyFp.Frobenius
import HexPolyFp.ModCompose

/-!
Core conformance checks for the `HexPolyFp` Frobenius and modular-composition
surface.

Oracle: none
Mode: always
Covered operations:
- `powModMonic`
- `frobeniusXMod`
- `frobeniusXPowMod`
- `composeModMonic`
Covered properties:
- modular exponentiation by exponent zero returns the quotient-ring identity
- Frobenius-power exponent zero agrees with reduction of `X`
- composition with the identity polynomial reduces the source polynomial
- composition of the zero polynomial is zero
Covered edge cases:
- constant monic modulus `1`
- the indeterminate `X` and constant polynomial inputs
- reductions modulo `x^2 + 2` over `F_5`
- linear modulus `x + 3` over `F_5`
- sparse inputs with internal zero coefficients
-/

namespace Hex
namespace FpPoly

private instance conformanceBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def constModulus : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5)]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem constModulus_monic : DensePoly.Monic constModulus := by
  rfl

private def linearModulus : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem linearModulus_monic : DensePoly.Monic linearModulus := by
  rfl

private def quadModulus : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem quadModulus_monic : DensePoly.Monic quadModulus := by
  rfl

-- `#eval` requires all of `DensePoly`'s propositional fields to be
-- non-sorry; `DensePoly.ofCoeffs` currently has a sorry-backed proof field.
/-- info: [0, 1] -/
#guard_msgs in
#eval! coeffNats (powModMonic (polyFive #[1, 1]) quadModulus quadModulus_monic 3)

#guard coeffNats (powModMonic (polyFive #[4, 2]) constModulus constModulus_monic 5) = []
#guard coeffNats (powModMonic (polyFive #[0, 0, 1]) quadModulus quadModulus_monic 0) = [1]
#guard coeffNats (powModMonic (polyFive #[0, 0, 1]) quadModulus quadModulus_monic 4) = [1]

/-- info: [0, 4] -/
#guard_msgs in
#eval! coeffNats (frobeniusXMod quadModulus quadModulus_monic)

#guard coeffNats (frobeniusXMod constModulus constModulus_monic) = []
#guard coeffNats (frobeniusXMod linearModulus linearModulus_monic) = [2]

/-- info: [0, 1] -/
#guard_msgs in
#eval! coeffNats (frobeniusXPowMod quadModulus quadModulus_monic 0)

#guard coeffNats (frobeniusXPowMod constModulus constModulus_monic 3) = []
#guard coeffNats (frobeniusXPowMod linearModulus linearModulus_monic 2) = [2]

/-- info: [4, 4] -/
#guard_msgs in
#eval! coeffNats
    (composeModMonic (polyFive #[3, 2, 1]) (polyFive #[1, 1]) quadModulus
      quadModulus_monic)

#guard coeffNats
    (composeModMonic (polyFive #[2, 4]) (polyFive #[3, 1]) constModulus
      constModulus_monic) = []
#guard coeffNats (composeModMonic (polyFive #[0, 0, 1]) X quadModulus quadModulus_monic) =
  [3]
#guard composeModMonic 0 (polyFive #[1, 1]) quadModulus quadModulus_monic = 0
#guard composeModMonic (polyFive #[0, 0, 1]) X quadModulus quadModulus_monic =
  modByMonic quadModulus (polyFive #[0, 0, 1]) quadModulus_monic

end FpPoly
end Hex
