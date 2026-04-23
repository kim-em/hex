import HexGfqRing.Instances

/-!
# `HexGfqRing` -- core conformance

Deterministic Lean-only conformance checks for the canonical
quotient-representation boundary of `HexGfqRing`.

**Conformance contract for this slice:**

- **Oracle:** `none`. This `core` profile uses committed small-prime
  examples together with the library's own representative formulas and
  reduction invariants.
- **Mode:** `always`.
- **Covered operations:** `HexGfqRing.reduceMod`, `HexGfqRing.ofPoly`,
  `HexGfqRing.repr`, quotient addition, quotient negation, quotient
  subtraction, quotient multiplication, quotient exponentiation.
- **Covered properties:**
  - `ofPoly` stores `reduceMod`'s canonical representative on committed
    examples;
  - stored representatives stay reduced under another `reduceMod`
    pass on committed examples;
  - the top-level `repr_add`, `repr_neg`, `repr_sub`, `repr_mul`, and
    `repr_pow` formulas agree with the reduced arithmetic formulas on
    committed examples.
- **Covered edge cases:** zero-polynomial inputs, a linear modulus, a
  `pow` exponent of `0`, and trailing-zero coefficient arrays that must
  normalize before quotient reduction.
-/

namespace HexGfqRing
namespace Conformance

open HexModArith
open HexPolyFp
open HexPolyFp.FpPoly

private abbrev P3 := HexPolyFp.FpPoly 3
private abbrev P5 := HexPolyFp.FpPoly 5

private def coeffsToNat {p : Nat} [NeZero p] (f : HexPolyFp.FpPoly p) : List Nat :=
  f.coeffs.toList.map fun a => a.toNat

private def poly3 (xs : List Nat) : P3 :=
  HexPolyFp.FpPoly.ofCoeffs ((xs.map fun n : Nat => (n : ZMod64 3)).toArray)

private def poly5 (xs : List Nat) : P5 :=
  HexPolyFp.FpPoly.ofCoeffs ((xs.map fun n : Nat => (n : ZMod64 5)).toArray)

private def typicalModulus : P5 := poly5 [2, 0, 1]
private def edgeModulus : P3 := poly3 [1, 1]
private def adversarialModulus : P3 := poly3 [2, 1, 1]

private theorem typicalModulus_pos : 0 < typicalModulus.degree := by decide
private theorem edgeModulus_pos : 0 < edgeModulus.degree := by decide
private theorem adversarialModulus_pos : 0 < adversarialModulus.degree := by decide

private def reduceTypicalInput : P5 := poly5 [3, 4, 1]
private def reduceEdgeInput : P3 := 0
private def reduceAdversarialInput : P3 := poly3 [2, 0, 0, 1, 0, 0]

private def typicalX : PolyQuotient 5 typicalModulus typicalModulus_pos :=
  ofPoly (f := typicalModulus) typicalModulus_pos reduceTypicalInput

private def typicalY : PolyQuotient 5 typicalModulus typicalModulus_pos :=
  ofPoly (f := typicalModulus) typicalModulus_pos (poly5 [1, 2])

private def edgeX : PolyQuotient 3 edgeModulus edgeModulus_pos :=
  ofPoly (f := edgeModulus) edgeModulus_pos (poly3 [0, 2, 0, 0])

private def edgeY : PolyQuotient 3 edgeModulus edgeModulus_pos :=
  ofPoly (f := edgeModulus) edgeModulus_pos (poly3 [1])

private def adversarialX : PolyQuotient 3 adversarialModulus adversarialModulus_pos :=
  ofPoly (f := adversarialModulus) adversarialModulus_pos reduceAdversarialInput

private def adversarialY : PolyQuotient 3 adversarialModulus adversarialModulus_pos :=
  ofPoly (f := adversarialModulus) adversarialModulus_pos (poly3 [1, 2, 1])

-- `#eval` must bypass sorry-bearing proof fields in `DensePoly` and
-- `PolyQuotient` while still evaluating the executable representative.

/-! ## `reduceMod` -/

/-- info: [1, 4] -/
#guard_msgs in
#eval! coeffsToNat (reduceMod typicalModulus reduceTypicalInput)

/-- info: [] -/
#guard_msgs in
#eval! coeffsToNat (reduceMod edgeModulus reduceEdgeInput)

/-- info: [1, 2] -/
#guard_msgs in
#eval! coeffsToNat (reduceMod adversarialModulus reduceAdversarialInput)

#guard coeffsToNat (reduceMod typicalModulus (reduceMod typicalModulus reduceTypicalInput)) =
  coeffsToNat (reduceMod typicalModulus reduceTypicalInput)
#guard coeffsToNat (reduceMod edgeModulus (reduceMod edgeModulus reduceEdgeInput)) =
  coeffsToNat (reduceMod edgeModulus reduceEdgeInput)
#guard coeffsToNat (reduceMod adversarialModulus (reduceMod adversarialModulus reduceAdversarialInput)) =
  coeffsToNat (reduceMod adversarialModulus reduceAdversarialInput)

/-! ## `ofPoly` and `repr` -/

/-- info: [1, 4] -/
#guard_msgs in
#eval! coeffsToNat (repr typicalX)

/-- info: [1] -/
#guard_msgs in
#eval! coeffsToNat (repr edgeX)

/-- info: [1, 2] -/
#guard_msgs in
#eval! coeffsToNat (repr adversarialX)

#guard coeffsToNat (repr typicalX) = coeffsToNat (reduceMod typicalModulus reduceTypicalInput)
#guard coeffsToNat (reduceMod typicalModulus (repr typicalX)) = coeffsToNat (repr typicalX)

#guard coeffsToNat (repr edgeX) = coeffsToNat (reduceMod edgeModulus (poly3 [0, 2, 0, 0]))
#guard coeffsToNat (reduceMod edgeModulus (repr edgeX)) = coeffsToNat (repr edgeX)

#guard coeffsToNat (repr adversarialX) = coeffsToNat (reduceMod adversarialModulus reduceAdversarialInput)
#guard coeffsToNat (reduceMod adversarialModulus (repr adversarialX)) = coeffsToNat (repr adversarialX)

/-! ## Quotient representative formulas -/

/-- info: [2, 1] -/
#guard_msgs in
#eval! coeffsToNat (repr (typicalX + typicalY))

/-- info: [2] -/
#guard_msgs in
#eval! coeffsToNat (repr (edgeX + edgeY))

/-- info: [] -/
#guard_msgs in
#eval! coeffsToNat (repr (adversarialX + adversarialY))

#guard coeffsToNat (repr (typicalX + typicalY)) =
  coeffsToNat (reduceMod typicalModulus (repr typicalX + repr typicalY))
#guard coeffsToNat (repr (edgeX + edgeY)) =
  coeffsToNat (reduceMod edgeModulus (repr edgeX + repr edgeY))
#guard coeffsToNat (repr (adversarialX + adversarialY)) =
  coeffsToNat (reduceMod adversarialModulus (repr adversarialX + repr adversarialY))

/-- info: [4, 1] -/
#guard_msgs in
#eval! coeffsToNat (repr (-typicalX))

/-- info: [2] -/
#guard_msgs in
#eval! coeffsToNat (repr (-edgeX))

/-- info: [2, 1] -/
#guard_msgs in
#eval! coeffsToNat (repr (-adversarialX))

#guard coeffsToNat (repr (-typicalX)) =
  coeffsToNat (reduceMod typicalModulus (0 - repr typicalX))
#guard coeffsToNat (repr (-edgeX)) =
  coeffsToNat (reduceMod edgeModulus (0 - repr edgeX))
#guard coeffsToNat (repr (-adversarialX)) =
  coeffsToNat (reduceMod adversarialModulus (0 - repr adversarialX))

/-- info: [0, 2] -/
#guard_msgs in
#eval! coeffsToNat (repr (typicalX - typicalY))

/-- info: [] -/
#guard_msgs in
#eval! coeffsToNat (repr (edgeX - edgeY))

/-- info: [2, 1] -/
#guard_msgs in
#eval! coeffsToNat (repr (adversarialX - adversarialY))

#guard coeffsToNat (repr (typicalX - typicalY)) =
  coeffsToNat (reduceMod typicalModulus (repr typicalX - repr typicalY))
#guard coeffsToNat (repr (edgeX - edgeY)) =
  coeffsToNat (reduceMod edgeModulus (repr edgeX - repr edgeY))
#guard coeffsToNat (repr (adversarialX - adversarialY)) =
  coeffsToNat (reduceMod adversarialModulus (repr adversarialX - repr adversarialY))

/-- info: [0, 1] -/
#guard_msgs in
#eval! coeffsToNat (repr (typicalX * typicalY))

/-- info: [1] -/
#guard_msgs in
#eval! coeffsToNat (repr (edgeX * edgeY))

/-- info: [1] -/
#guard_msgs in
#eval! coeffsToNat (repr (adversarialX * adversarialY))

#guard coeffsToNat (repr (typicalX * typicalY)) =
  coeffsToNat (reduceMod typicalModulus (repr typicalX * repr typicalY))
#guard coeffsToNat (repr (edgeX * edgeY)) =
  coeffsToNat (reduceMod edgeModulus (repr edgeX * repr edgeY))
#guard coeffsToNat (repr (adversarialX * adversarialY)) =
  coeffsToNat (reduceMod adversarialModulus (repr adversarialX * repr adversarialY))

/-- info: [0, 4] -/
#guard_msgs in
#eval! coeffsToNat (repr (typicalX ^ 3))

/-- info: [1] -/
#guard_msgs in
#eval! coeffsToNat (repr (edgeX ^ 0))

/-- info: [1] -/
#guard_msgs in
#eval! coeffsToNat (repr (adversarialX ^ 4))

#guard coeffsToNat (repr (typicalX ^ 3)) =
  coeffsToNat (reduceMod typicalModulus (HexPolyFp.FpPoly.powModMonic (repr typicalX) 3 typicalModulus))
#guard coeffsToNat (repr (edgeX ^ 0)) =
  coeffsToNat (reduceMod edgeModulus (HexPolyFp.FpPoly.powModMonic (repr edgeX) 0 edgeModulus))
#guard coeffsToNat (repr (adversarialX ^ 4)) =
  coeffsToNat
    (reduceMod adversarialModulus (HexPolyFp.FpPoly.powModMonic (repr adversarialX) 4 adversarialModulus))

end Conformance
end HexGfqRing
