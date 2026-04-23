import HexModArith.Theorems

/-!
Deterministic core conformance checks for `HexModArith`.

- Oracle: `none`. Lean's `Nat` modular arithmetic is the property
  oracle for this Phase 3 core slice.
- Mode: `always`.
- Covered operations:
  - `HexModArith.ZMod64.ofNat`
  - `HexModArith.ZMod64.add`
  - `HexModArith.ZMod64.sub`
  - `HexModArith.ZMod64.mul`
  - `HexModArith.ZMod64.inv?`
  - `HexModArith.ZMod64.pow`
- Covered properties:
  - `ofNat` canonicalizes representatives by reduction modulo `p`.
  - `add`, `sub`, `mul`, and `pow` agree with the corresponding
    `Nat` modular arithmetic formulas on committed inputs.
  - `inv?` returns the expected inverse for committed units and
    `none` for committed non-units.
  - On committed invertible residues, the returned inverse multiplies
    with the original residue to `1`.
  - `add` preserves the zero identity, `mul` preserves the one
    identity, and `pow a 0 = 1` on committed inputs.
- Covered edge cases:
  - modulus `1`
  - zero representatives
  - additive wraparound near the modulus
  - subtraction underflow
  - exponent `0`
  - residues at `p - 1`
-/

namespace HexModArith
namespace Conformance

private def z1 (n : Nat) : ZMod64 1 :=
  ZMod64.ofNat 1 n (by decide)

private def z17 (n : Nat) : ZMod64 17 :=
  ZMod64.ofNat 17 n (by decide)

private def z97 (n : Nat) : ZMod64 97 :=
  ZMod64.ofNat 97 n (by decide)

private def zero17 : ZMod64 17 :=
  ZMod64.zero 17 (by decide)

private def one17 : ZMod64 17 :=
  ZMod64.one 17 (by decide)

private def one97 : ZMod64 97 :=
  ZMod64.one 97 (by decide)

private def invToNat? {p : Nat} (a : ZMod64 p) : Option Nat :=
  Option.map ZMod64.toNat (ZMod64.inv? a)

/-! ## `ZMod64.ofNat` -/

/-- info: 3 -/
#guard_msgs in #eval (z17 20).toNat

/-- info: 0 -/
#guard_msgs in #eval (z1 7).toNat

/-- info: 96 -/
#guard_msgs in #eval (z97 (97 * 123 + 96)).toNat

#guard (z17 20).toNat = 20 % 17
#guard (z1 7).toNat = 7 % 1
#guard (z97 (97 * 123 + 96)).toNat = (97 * 123 + 96) % 97

/-! ## `ZMod64.add` -/

/-- info: 2 -/
#guard_msgs in #eval (ZMod64.add (z17 5) (z17 14)).toNat

/-- info: 0 -/
#guard_msgs in #eval (ZMod64.add (z1 0) (z1 0)).toNat

/-- info: 95 -/
#guard_msgs in #eval (ZMod64.add (z97 96) (z97 96)).toNat

#guard (ZMod64.add (z17 5) (z17 14)).toNat = (5 + 14) % 17
#guard (ZMod64.add (z1 0) (z1 0)).toNat = (0 + 0) % 1
#guard (ZMod64.add (z97 96) (z97 96)).toNat = (96 + 96) % 97
#guard (ZMod64.add (z17 5) zero17).toNat = (z17 5).toNat

/-! ## `ZMod64.sub` -/

/-- info: 8 -/
#guard_msgs in #eval (ZMod64.sub (z17 5) (z17 14)).toNat

/-- info: 0 -/
#guard_msgs in #eval (ZMod64.sub (z1 0) (z1 0)).toNat

/-- info: 4 -/
#guard_msgs in #eval (ZMod64.sub (z97 3) (z97 96)).toNat

#guard (ZMod64.sub (z17 5) (z17 14)).toNat = (5 + 17 - 14) % 17
#guard (ZMod64.sub (z1 0) (z1 0)).toNat = (0 + 1 - 0) % 1
#guard (ZMod64.sub (z97 3) (z97 96)).toNat = (3 + 97 - 96) % 97

/-! ## `ZMod64.mul` -/

/-- info: 2 -/
#guard_msgs in #eval (ZMod64.mul (z17 5) (z17 14)).toNat

/-- info: 0 -/
#guard_msgs in #eval (ZMod64.mul (z1 0) (z1 0)).toNat

/-- info: 1 -/
#guard_msgs in #eval (ZMod64.mul (z97 96) (z97 96)).toNat

#guard (ZMod64.mul (z17 5) (z17 14)).toNat = (5 * 14) % 17
#guard (ZMod64.mul (z1 0) (z1 0)).toNat = (0 * 0) % 1
#guard (ZMod64.mul (z97 96) (z97 96)).toNat = (96 * 96) % 97
#guard (ZMod64.mul (z97 96) one97).toNat = (z97 96).toNat

/-! ## `ZMod64.inv?` -/

/-- info: some 7 -/
#guard_msgs in #eval invToNat? (z17 5)

/-- info: none -/
#guard_msgs in #eval invToNat? zero17

/-- info: some 96 -/
#guard_msgs in #eval invToNat? (z97 96)

/-- info: some 21 -/
#guard_msgs in #eval invToNat? (z97 37)

#guard invToNat? (z17 5) = some 7
#guard invToNat? zero17 = none
#guard invToNat? (z97 96) = some 96
#guard invToNat? (z97 37) = some 21
#guard match ZMod64.inv? (z17 5) with
  | some b => (ZMod64.mul b (z17 5)).toNat = one17.toNat
  | none => false
#guard match ZMod64.inv? (z97 96) with
  | some b => (ZMod64.mul b (z97 96)).toNat = one97.toNat
  | none => false
#guard match ZMod64.inv? (z97 37) with
  | some b => (ZMod64.mul b (z97 37)).toNat = one97.toNat
  | none => false

/-! ## `ZMod64.pow` -/

/-- info: 6 -/
#guard_msgs in #eval (ZMod64.pow (z17 5) 3).toNat

/-- info: 0 -/
#guard_msgs in #eval (ZMod64.pow (z1 7) 5).toNat

/-- info: 1 -/
#guard_msgs in #eval (ZMod64.pow (z97 96) 2).toNat

#guard (ZMod64.pow (z17 5) 3).toNat = 5 ^ 3 % 17
#guard (ZMod64.pow (z1 7) 5).toNat = 7 ^ 5 % 1
#guard (ZMod64.pow (z97 96) 2).toNat = 96 ^ 2 % 97
#guard (ZMod64.pow (z17 5) 0).toNat = one17.toNat

end Conformance
end HexModArith
