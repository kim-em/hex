import HexPolyFp.Frobenius
import HexPolyFp.ModCompose
import HexPolyFp.SquareFree

/-!
Core conformance checks for the `HexPolyFp` Frobenius, modular-composition,
and square-free decomposition surface.

Oracle: none
Mode: always
Covered operations:
- `powModMonic`
- `frobeniusXMod`
- `frobeniusXPowMod`
- `composeModMonic`
- `squareFreeDecomposition`
- `weightedProduct`
Covered properties:
- modular exponentiation by exponent zero returns the quotient-ring identity
- Frobenius-power exponent zero agrees with reduction of `X`
- composition with the identity polynomial reduces the source polynomial
- composition of the zero polynomial is zero
- square-free decompositions reconstruct the input from the unit and weighted factors
- weighted products respect positive multiplicities
Covered edge cases:
- constant monic modulus `1`
- the indeterminate `X` and constant polynomial inputs
- reductions modulo `x^2 + 2` over `F_5`
- linear modulus `x + 3` over `F_5`
- sparse inputs with internal zero coefficients
- square-free, repeated-factor, derivative-zero, zero, and scalar square-free inputs
-/

namespace Hex
namespace FpPoly

private instance conformanceBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem prime_five : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def sfFactorFive (coeffs : Array Nat) (multiplicity : Nat) : SquareFreeFactor 5 :=
  { factor := polyFive coeffs, multiplicity }

private def sfSummary (d : SquareFreeDecomposition 5) : Nat × List (List Nat × Nat) :=
  (d.unit.toNat, d.factors.map (fun sf => (coeffNats sf.factor, sf.multiplicity)))

private def sfReconstruction (d : SquareFreeDecomposition 5) : FpPoly 5 :=
  DensePoly.C d.unit * weightedProduct d.factors

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

/-- info: [1, 1, 1] -/
#guard_msgs in
#eval! coeffNats (weightedProduct [sfFactorFive #[4, 4, 4] 1, sfFactorFive #[2] 2])

#guard coeffNats (weightedProduct [sfFactorFive #[1, 1] 2]) = [1, 2, 1]
#guard coeffNats (weightedProduct [sfFactorFive #[1, 1] 5]) = [1, 0, 0, 0, 0, 1]
#guard coeffNats (weightedProduct ([] : List (SquareFreeFactor 5))) = [1]

/-- info: (1, [([4, 4, 4], 1), ([2], 2)]) -/
#guard_msgs in
#eval! sfSummary (squareFreeDecomposition prime_five (polyFive #[1, 1, 1]))

#guard
  let f := polyFive #[1, 1, 1]
  coeffNats (sfReconstruction (squareFreeDecomposition prime_five f)) = coeffNats f

/-- info: (1, [([4], 1), ([2, 2], 2)]) -/
#guard_msgs in
#eval! sfSummary (squareFreeDecomposition prime_five (polyFive #[1, 2, 1]))

#guard
  let f := polyFive #[1, 2, 1]
  coeffNats (sfReconstruction (squareFreeDecomposition prime_five f)) = coeffNats f

/-- info: (1, [([1, 1], 5)]) -/
#guard_msgs in
#eval! sfSummary (squareFreeDecomposition prime_five (polyFive #[1, 0, 0, 0, 0, 1]))

#guard
  let f := polyFive #[1, 0, 0, 0, 0, 1]
  coeffNats (sfReconstruction (squareFreeDecomposition prime_five f)) = coeffNats f

#guard sfSummary (squareFreeDecomposition prime_five (0 : FpPoly 5)) = (0, [])
#guard
  let f := polyFive #[3]
  sfSummary (squareFreeDecomposition prime_five f) = (3, []) ∧
    coeffNats (sfReconstruction (squareFreeDecomposition prime_five f)) = coeffNats f

end FpPoly
end Hex
