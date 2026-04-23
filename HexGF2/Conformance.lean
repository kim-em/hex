import HexGF2.GF2n
import HexGF2.GF2nPoly

/-!
# `HexGF2` -- packed-core, Euclidean, and extension-field conformance

Deterministic Lean-only conformance checks for the packed `GF(2)`
core arithmetic surface.

**Conformance contract for this slice:**

- **Oracle:** `none`.
- **Mode:** `always`.
- **Covered operations:** `Hex.pureClmul`, `HexGF2.clmul`,
  `GF2Poly.ofWords`, packed XOR addition, `GF2Poly.shiftLeft`,
  `GF2Poly.shiftRight`, `GF2Poly.divMod`, `(/)`, `(%)`,
  `GF2Poly.gcd`, `GF2Poly.xgcd`, `GF2n` `0` / `1` / `(+)` /
  `(*)` / `Inv.inv`, `GF2nPoly` `0` / `1` / `(+)` / `(*)` /
  `Inv.inv` / `(/)`.
- **Covered properties:**
  - `HexGF2.clmul` agrees with the pure-Lean `Hex.pureClmul`
    reference semantics on committed fixtures;
  - `GF2Poly.ofWords` normalizes trailing zero words into the
    canonical packed representation;
  - packed addition agrees with `GF2Poly.xorWords` on committed
    fixtures;
  - left and right shifts agree with `GF2Poly.shiftLeftWords` and
    `GF2Poly.shiftRightWords` on committed fixtures;
  - `GF2Poly.divMod` reconstructs the dividend from quotient and
    remainder on committed nonzero-divisor fixtures, and division by
    zero falls back to zero quotient plus the original dividend as
    remainder;
  - nonzero packed remainders have degree strictly smaller than the
    committed divisor;
  - `GF2Poly.gcd` agrees with the `gcd` field of `GF2Poly.xgcd` on
    committed fixtures;
  - packed `GF2Poly.xgcd` data satisfies the committed Bezout
    identity;
  - committed `GF2n` and `GF2nPoly` fixtures serialize to the
    expected reduced representatives for `0`, `1`, addition,
    multiplication, and one inverse-or-division path on each
    carrier;
  - committed `GF2n` and `GF2nPoly` fixtures satisfy
    characteristic-two cancellation (`x + x = 0`, `x - x = 0`) and
    the nonzero inverse contract.
- **Covered edge cases:** zero inputs for carry-less multiply,
  empty packed words, cancellation to zero under XOR addition, and
  cross-word carry / borrow behavior for bit shifts, division by the
  zero polynomial, a zero left Euclidean input, a nonzero
  remainder Euclidean step, the packed extension-field zero / one
  representatives, and a quotient-field division fixture whose
  result reduces modulo the committed irreducible polynomial.
-/

namespace HexGF2
namespace Conformance

private def serializeClmul (product : UInt64 × UInt64) : Nat × Nat :=
  (product.1.toNat, product.2.toNat)

private def serializePoly (f : GF2Poly) : List Nat × Nat :=
  (f.words.toList.map UInt64.toNat, f.degree)

private def serializeDivMod (result : GF2Poly.DivMod) :
    (List Nat × Nat) × (List Nat × Nat) :=
  (serializePoly result.quotient, serializePoly result.remainder)

private def serializeXgcd (result : GF2Poly.Xgcd) :
    (List Nat × Nat) × (List Nat × Nat) × (List Nat × Nat) :=
  (serializePoly result.gcd, serializePoly result.s, serializePoly result.t)

private def serializeGF2n {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}
    (x : GF2n n irr hn hn64 hirr) : Nat :=
  x.val.toNat

private def gf2nIrr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x3 3) := by
  simp [GF2Poly.Irreducible, GF2Poly.IsZero, GF2Poly.ofUInt64Monic]

private theorem gf2nPos : 0 < 3 := by
  decide

private theorem gf2nLt64 : 3 < 64 := by
  decide

private abbrev GF2nFixture :=
  GF2n 3 0x3 gf2nPos gf2nLt64 gf2nIrr

private def gf2nTypical : GF2nFixture :=
  { val := 0x5
    val_lt := by decide }

private def gf2nTypicalRight : GF2nFixture :=
  { val := 0x7
    val_lt := by decide }

private def gf2nInvFixture : GF2nFixture :=
  { val := 0x3
    val_lt := by decide }

private def gf2nPolyModulus : GF2Poly :=
  GF2Poly.ofUInt64Monic 0x3 3

private abbrev GF2nPolyFixture :=
  GF2nPoly gf2nPolyModulus gf2nIrr

private def gf2nPolyTypical : GF2nPolyFixture :=
  GF2nPoly.ofPoly (f := gf2nPolyModulus) (GF2Poly.ofWords #[0x3]) gf2nIrr

private def gf2nPolyTypicalRight : GF2nPolyFixture :=
  GF2nPoly.ofPoly (f := gf2nPolyModulus) (GF2Poly.ofWords #[0x5]) gf2nIrr

private def gf2nPolyInvFixture : GF2nPolyFixture :=
  GF2nPoly.ofPoly (f := gf2nPolyModulus) (GF2Poly.ofWords #[0x2]) gf2nIrr

private def ofWordsTypicalInput : Array UInt64 :=
  #[0x13, 0x80]

private def ofWordsEdgeInput : Array UInt64 :=
  #[]

private def ofWordsAdversarialInput : Array UInt64 :=
  #[0x1, 0x0, 0x0]

private def addTypicalLeft : GF2Poly :=
  GF2Poly.ofWords #[0x13, 0x80]

private def addTypicalRight : GF2Poly :=
  GF2Poly.ofWords #[0x7, 0x3]

private def addEdgeLeft : GF2Poly :=
  GF2Poly.ofWords #[]

private def addEdgeRight : GF2Poly :=
  GF2Poly.ofWords #[0x9]

private def addAdversarialLeft : GF2Poly :=
  GF2Poly.ofWords #[0x5, 0x1]

private def addAdversarialRight : GF2Poly :=
  GF2Poly.ofWords #[0x5, 0x1]

private def shiftTypical : GF2Poly :=
  GF2Poly.ofWords #[0x13, 0x80]

private def shiftEdge : GF2Poly :=
  GF2Poly.ofWords #[]

private def shiftLeftAdversarial : GF2Poly :=
  GF2Poly.ofWords #[0x8000000000000000]

private def shiftRightAdversarial : GF2Poly :=
  GF2Poly.ofWords #[0x0, 0x1]

private def euclidTypicalDividend : GF2Poly :=
  GF2Poly.ofWords #[0x1b]

private def euclidTypicalDivisor : GF2Poly :=
  GF2Poly.ofWords #[0x5]

private def euclidEdgeDividend : GF2Poly :=
  GF2Poly.ofWords #[0x9]

private def euclidEdgeDivisor : GF2Poly :=
  GF2Poly.ofWords #[]

private def euclidAdversarialDividend : GF2Poly :=
  GF2Poly.ofWords #[0x15]

private def euclidAdversarialDivisor : GF2Poly :=
  GF2Poly.ofWords #[0x6]

private def euclidZeroLeft : GF2Poly :=
  GF2Poly.ofWords #[]

/-! ## `pureClmul` and `clmul` -/

/- `clmul` is attached to an extern, so spot values run through the
pure-Lean reference and agreement with `clmul` is checked by
elaboration-time definitional equality. -/

/-- info: (0, 173) -/
#guard_msgs in
#eval serializeClmul (Hex.pureClmul 0x13 0xb)

/-- info: (0, 0) -/
#guard_msgs in
#eval serializeClmul (Hex.pureClmul 0x0 0xdeadbeef)

/-- info: (1, 9223372036854775811) -/
#guard_msgs in
#eval serializeClmul (Hex.pureClmul 0x8000000000000001 0x3)

example : clmul 0x13 0xb = Hex.pureClmul 0x13 0xb := by
  rfl

example : clmul 0x0 0xdeadbeef = Hex.pureClmul 0x0 0xdeadbeef := by
  rfl

example : clmul 0x8000000000000001 0x3 = Hex.pureClmul 0x8000000000000001 0x3 := by
  rfl

/-! ## `ofWords` normalization -/

-- `#eval!` is required here because `GF2Poly.ofWords` stores a
-- sorry-backed `wf` proof field in the resulting structure.
/-- info: ([19, 128], 71) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.ofWords ofWordsTypicalInput)

/-- info: ([], 0) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.ofWords ofWordsEdgeInput)

/-- info: ([1], 0) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.ofWords ofWordsAdversarialInput)

example : GF2Poly.ofWords #[] = GF2Poly.ofWords (GF2Poly.normalizeWords #[]) := by
  rfl

/-! ## Packed XOR addition -/

/-- info: ([20, 131], 71) -/
#guard_msgs in
#eval! serializePoly (addTypicalLeft + addTypicalRight)

/-- info: ([9], 3) -/
#guard_msgs in
#eval! serializePoly (addEdgeLeft + addEdgeRight)

/-- info: ([], 0) -/
#guard_msgs in
#eval! serializePoly (addAdversarialLeft + addAdversarialRight)

example :
    addTypicalLeft + addTypicalRight =
      GF2Poly.ofWords (GF2Poly.xorWords addTypicalLeft.words addTypicalRight.words) := by
  simpa using GF2Poly.add_eq_ofWords addTypicalLeft addTypicalRight

/-! ## Shift operations -/

/-- info: ([38, 256], 72) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.shiftLeft shiftTypical 1)

/-- info: ([], 0) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.shiftLeft shiftEdge 17)

/-- info: ([0, 1], 64) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.shiftLeft shiftLeftAdversarial 1)

/-- info: ([9, 64], 70) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.shiftRight shiftTypical 1)

/-- info: ([], 0) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.shiftRight shiftEdge 17)

/-- info: ([1], 0) -/
#guard_msgs in
#eval! serializePoly (GF2Poly.shiftRight shiftRightAdversarial 64)

example :
    GF2Poly.shiftLeft shiftTypical 1 =
      GF2Poly.ofWords (GF2Poly.shiftLeftWords shiftTypical.words 1) := by
  simpa using GF2Poly.shiftLeft_eq_ofWords shiftTypical 1

example :
    GF2Poly.shiftRight shiftTypical 1 =
      GF2Poly.ofWords (GF2Poly.shiftRightWords shiftTypical.words 1) := by
  simpa using GF2Poly.shiftRight_eq_ofWords shiftTypical 1

/-! ## Packed Euclidean operations -/

-- `#eval!` is required here because `GF2Poly`, `DivMod`, and `Xgcd`
-- all transitively carry sorry-backed packed-normalization proofs.
/-- info: (([7], 2), [], 0) -/
#guard_msgs in
#eval! serializeDivMod (GF2Poly.divMod euclidTypicalDividend euclidTypicalDivisor)

/-- info: (([], 0), [9], 3) -/
#guard_msgs in
#eval! serializeDivMod (GF2Poly.divMod euclidEdgeDividend euclidEdgeDivisor)

/-- info: (([6], 2), [1], 0) -/
#guard_msgs in
#eval! serializeDivMod (GF2Poly.divMod euclidAdversarialDividend euclidAdversarialDivisor)

/-- info: ([7], 2) -/
#guard_msgs in
#eval! serializePoly (euclidTypicalDividend / euclidTypicalDivisor)

/-- info: ([], 0) -/
#guard_msgs in
#eval! serializePoly (euclidEdgeDividend / euclidEdgeDivisor)

/-- info: ([6], 2) -/
#guard_msgs in
#eval! serializePoly (euclidAdversarialDividend / euclidAdversarialDivisor)

/-- info: ([], 0) -/
#guard_msgs in
#eval! serializePoly (euclidTypicalDividend % euclidTypicalDivisor)

/-- info: ([9], 3) -/
#guard_msgs in
#eval! serializePoly (euclidEdgeDividend % euclidEdgeDivisor)

/-- info: ([1], 0) -/
#guard_msgs in
#eval! serializePoly (euclidAdversarialDividend % euclidAdversarialDivisor)

example :
    serializePoly
        (euclidTypicalDivisor * (GF2Poly.divMod euclidTypicalDividend euclidTypicalDivisor).quotient +
          (GF2Poly.divMod euclidTypicalDividend euclidTypicalDivisor).remainder) =
      serializePoly euclidTypicalDividend := by
  decide

#guard let data := GF2Poly.divMod euclidEdgeDividend euclidEdgeDivisor
  data.quotient.words = #[] ∧
    serializePoly data.remainder = serializePoly euclidEdgeDividend

#guard let remainder := euclidAdversarialDividend % euclidAdversarialDivisor
  remainder.words ≠ #[] ∧ remainder.degree < euclidAdversarialDivisor.degree

example :
    serializePoly (GF2Poly.gcd euclidTypicalDividend euclidTypicalDivisor) = ([5], 2) := by
  decide

example :
    serializePoly (GF2Poly.gcd euclidZeroLeft euclidTypicalDivisor) = ([5], 2) := by
  decide

example :
    serializePoly (GF2Poly.gcd euclidAdversarialDividend euclidAdversarialDivisor) = ([1], 0) := by
  decide

example :
    serializeXgcd (GF2Poly.xgcd euclidTypicalDividend euclidTypicalDivisor) =
      (([5], 2), ([], 0), ([1], 0)) := by
  decide

example :
    serializeXgcd (GF2Poly.xgcd euclidZeroLeft euclidTypicalDivisor) =
      (([5], 2), ([], 0), ([1], 0)) := by
  decide

example :
    serializeXgcd (GF2Poly.xgcd euclidAdversarialDividend euclidAdversarialDivisor) =
      (([1], 0), ([1], 0), ([6], 2)) := by
  decide

example :
    serializePoly (GF2Poly.gcd euclidTypicalDividend euclidTypicalDivisor) =
      serializePoly (GF2Poly.xgcd euclidTypicalDividend euclidTypicalDivisor).gcd := by
  decide

example :
    serializePoly (GF2Poly.gcd euclidZeroLeft euclidTypicalDivisor) =
      serializePoly (GF2Poly.xgcd euclidZeroLeft euclidTypicalDivisor).gcd := by
  decide

example :
    serializePoly (GF2Poly.gcd euclidAdversarialDividend euclidAdversarialDivisor) =
      serializePoly (GF2Poly.xgcd euclidAdversarialDividend euclidAdversarialDivisor).gcd := by
  decide

example :
    serializePoly
        ((GF2Poly.xgcd euclidTypicalDividend euclidTypicalDivisor).s * euclidTypicalDividend +
          (GF2Poly.xgcd euclidTypicalDividend euclidTypicalDivisor).t * euclidTypicalDivisor) =
      serializePoly (GF2Poly.xgcd euclidTypicalDividend euclidTypicalDivisor).gcd := by
  decide

example :
    serializePoly
        ((GF2Poly.xgcd euclidZeroLeft euclidTypicalDivisor).s * euclidZeroLeft +
          (GF2Poly.xgcd euclidZeroLeft euclidTypicalDivisor).t * euclidTypicalDivisor) =
      serializePoly (GF2Poly.xgcd euclidZeroLeft euclidTypicalDivisor).gcd := by
  decide

example :
    serializePoly
        ((GF2Poly.xgcd euclidAdversarialDividend euclidAdversarialDivisor).s *
            euclidAdversarialDividend +
          (GF2Poly.xgcd euclidAdversarialDividend euclidAdversarialDivisor).t *
          euclidAdversarialDivisor) =
      serializePoly (GF2Poly.xgcd euclidAdversarialDividend euclidAdversarialDivisor).gcd := by
  decide

/-! ## `GF2n` extension arithmetic -/

-- `#eval!` is required here because `GF2n.ofUInt64` stores the
-- sorry-backed `val_lt` proof field in the resulting structure.
/-- info: 0 -/
#guard_msgs in
#eval! serializeGF2n (0 : GF2nFixture)

/-- info: 1 -/
#guard_msgs in
#eval! serializeGF2n (1 : GF2nFixture)

/-- info: 2 -/
#guard_msgs in
#eval! serializeGF2n (gf2nTypical + gf2nTypicalRight)

example : serializeGF2n (gf2nTypical * gf2nTypicalRight) = 6 := by
  decide

example : serializeGF2n (gf2nInvFixture⁻¹) = 6 := by
  decide

#guard serializeGF2n (gf2nTypical + gf2nTypical) = 0

#guard serializeGF2n (gf2nTypical - gf2nTypical) = 0

example :
    serializeGF2n gf2nInvFixture ≠ 0 ∧
      serializeGF2n (gf2nInvFixture * gf2nInvFixture⁻¹) = 1 := by
  decide

/-! ## `GF2nPoly` quotient arithmetic -/

-- `#eval!` is required here because `GF2nPoly.ofPoly` stores the
-- sorry-backed `val_reduced` proof field in the resulting structure.
/-- info: ([], 0) -/
#guard_msgs in
#eval! serializePoly ((0 : GF2nPolyFixture).val)

/-- info: ([1], 0) -/
#guard_msgs in
#eval! serializePoly ((1 : GF2nPolyFixture).val)

/-- info: ([6], 2) -/
#guard_msgs in
#eval! serializePoly ((gf2nPolyTypical + gf2nPolyTypicalRight).val)

example : serializePoly ((gf2nPolyTypical * gf2nPolyTypicalRight).val) = ([4], 2) := by
  decide

example : serializePoly ((gf2nPolyInvFixture⁻¹).val) = ([5], 2) := by
  decide

example : serializePoly ((gf2nPolyInvFixture / gf2nPolyTypicalRight).val) = ([4], 2) := by
  decide

#guard serializePoly ((gf2nPolyTypical + gf2nPolyTypical).val) = ([], 0)

#guard serializePoly ((gf2nPolyTypical - gf2nPolyTypical).val) = ([], 0)

example :
    serializePoly gf2nPolyInvFixture.val ≠ ([], 0) ∧
      serializePoly ((gf2nPolyInvFixture * gf2nPolyInvFixture⁻¹).val) = ([1], 0) := by
  decide

end Conformance
end HexGF2
