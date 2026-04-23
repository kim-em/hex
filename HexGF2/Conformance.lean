import HexGF2.Ops

/-!
# `HexGF2` -- packed-core conformance

Deterministic Lean-only conformance checks for the packed `GF(2)`
core arithmetic surface.

**Conformance contract for this slice:**

- **Oracle:** `none`.
- **Mode:** `always`.
- **Covered operations:** `Hex.pureClmul`, `HexGF2.clmul`,
  `GF2Poly.ofWords`, packed XOR addition, `GF2Poly.shiftLeft`,
  `GF2Poly.shiftRight`.
- **Covered properties:**
  - `HexGF2.clmul` agrees with the pure-Lean `Hex.pureClmul`
    reference semantics on committed fixtures;
  - `GF2Poly.ofWords` normalizes trailing zero words into the
    canonical packed representation;
  - packed addition agrees with `GF2Poly.xorWords` on committed
    fixtures;
  - left and right shifts agree with `GF2Poly.shiftLeftWords` and
    `GF2Poly.shiftRightWords` on committed fixtures.
- **Covered edge cases:** zero inputs for carry-less multiply,
  empty packed words, cancellation to zero under XOR addition, and
  cross-word carry / borrow behavior for bit shifts.
-/

namespace HexGF2
namespace Conformance

private def serializeClmul (product : UInt64 × UInt64) : Nat × Nat :=
  (product.1.toNat, product.2.toNat)

private def serializePoly (f : GF2Poly) : List Nat × Nat :=
  (f.words.toList.map UInt64.toNat, f.degree)

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

end Conformance
end HexGF2
