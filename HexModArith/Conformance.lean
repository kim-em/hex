import HexModArith.Core

/-!
# `HexModArith` — core conformance

Deterministic Lean-only conformance checks for the executable
`HexModArith.ZMod64` arithmetic surface. Every check elaborates as part
of `lake build HexModArith`, so regressions in canonical reduction or
modular arithmetic fail CI immediately.

**Conformance contract for this slice:**

- **Oracle:** `none`. The `core` profile uses Lean's `Nat` modular
  arithmetic as the property oracle on committed fixtures.
- **Mode:** `always`.
- **Covered operations:** `HexModArith.ZMod64.ofNat`,
  `HexModArith.ZMod64.add`, `HexModArith.ZMod64.sub`,
  `HexModArith.ZMod64.mul`, `HexModArith.ZMod64.pow`.
- **Covered properties:**
  - `ofNat` stores the canonical representative `n % p`;
  - addition, subtraction, multiplication, and exponentiation agree
    with the corresponding `Nat` arithmetic modulo `p` on committed
    fixtures;
  - all spot checks use the residue's `toNat` view so reviewers can see
    the canonical result directly.
- **Covered edge cases:** modulus `1`, zero residues, borrow in
  subtraction, multiplication by zero, exponent `0`, and a power-of-two
  modulus exercising the Barrett/fallback split boundary.
-/

namespace HexModArith
namespace Conformance
namespace ZMod64

private def mod17Typical : HexModArith.ZMod64 17 :=
  HexModArith.ZMod64.ofNat 17 23 (by decide)

private def mod17Other : HexModArith.ZMod64 17 :=
  HexModArith.ZMod64.ofNat 17 14 (by decide)

private def mod17Five : HexModArith.ZMod64 17 :=
  HexModArith.ZMod64.ofNat 17 5 (by decide)

private def mod17Zero : HexModArith.ZMod64 17 :=
  HexModArith.ZMod64.ofNat 17 0 (by decide)

private def mod16High : HexModArith.ZMod64 16 :=
  HexModArith.ZMod64.ofNat 16 15 (by decide)

private def mod16One : HexModArith.ZMod64 16 :=
  HexModArith.ZMod64.ofNat 16 1 (by decide)

private def mod16Three : HexModArith.ZMod64 16 :=
  HexModArith.ZMod64.ofNat 16 3 (by decide)

private def mod1Any : HexModArith.ZMod64 1 :=
  HexModArith.ZMod64.ofNat 1 42 (by decide)

/-! ## `ZMod64.ofNat` -/

/-- info: 6 -/
#guard_msgs in #eval mod17Typical.toNat

/-- info: 0 -/
#guard_msgs in #eval mod1Any.toNat

/-- info: 15 -/
#guard_msgs in #eval (HexModArith.ZMod64.ofNat 16 31 (by decide)).toNat

#guard mod17Typical.toNat = 23 % 17
#guard mod1Any.toNat = 42 % 1
#guard (HexModArith.ZMod64.ofNat 16 31 (by decide)).toNat = 31 % 16

/-! ## `ZMod64.add` -/

/-- info: 3 -/
#guard_msgs in #eval (HexModArith.ZMod64.add mod17Typical mod17Other).toNat

/-- info: 0 -/
#guard_msgs in #eval (HexModArith.ZMod64.add mod1Any mod1Any).toNat

/-- info: 14 -/
#guard_msgs in #eval (HexModArith.ZMod64.add mod16High mod16High).toNat

#guard (HexModArith.ZMod64.add mod17Typical mod17Other).toNat =
  (mod17Typical.toNat + mod17Other.toNat) % 17
#guard (HexModArith.ZMod64.add mod1Any mod1Any).toNat =
  (mod1Any.toNat + mod1Any.toNat) % 1
#guard (HexModArith.ZMod64.add mod16High mod16High).toNat =
  (mod16High.toNat + mod16High.toNat) % 16

/-! ## `ZMod64.sub` -/

/-- info: 9 -/
#guard_msgs in #eval (HexModArith.ZMod64.sub mod17Typical mod17Other).toNat

/-- info: 0 -/
#guard_msgs in #eval (HexModArith.ZMod64.sub mod1Any mod1Any).toNat

/-- info: 2 -/
#guard_msgs in #eval (HexModArith.ZMod64.sub mod16One mod16High).toNat

#guard (HexModArith.ZMod64.sub mod17Typical mod17Other).toNat =
  (mod17Typical.toNat + 17 - mod17Other.toNat) % 17
#guard (HexModArith.ZMod64.sub mod1Any mod1Any).toNat =
  (mod1Any.toNat + 1 - mod1Any.toNat) % 1
#guard (HexModArith.ZMod64.sub mod16One mod16High).toNat =
  (mod16One.toNat + 16 - mod16High.toNat) % 16

/-! ## `ZMod64.mul` -/

/-- info: 16 -/
#guard_msgs in #eval (HexModArith.ZMod64.mul mod17Typical mod17Other).toNat

/-- info: 0 -/
#guard_msgs in #eval (HexModArith.ZMod64.mul mod17Zero mod17Other).toNat

/-- info: 1 -/
#guard_msgs in #eval (HexModArith.ZMod64.mul mod16High mod16High).toNat

#guard (HexModArith.ZMod64.mul mod17Typical mod17Other).toNat =
  (mod17Typical.toNat * mod17Other.toNat) % 17
#guard (HexModArith.ZMod64.mul mod17Zero mod17Other).toNat =
  (mod17Zero.toNat * mod17Other.toNat) % 17
#guard (HexModArith.ZMod64.mul mod16High mod16High).toNat =
  (mod16High.toNat * mod16High.toNat) % 16

/-! ## `ZMod64.pow` -/

/-- info: 6 -/
#guard_msgs in #eval (HexModArith.ZMod64.pow mod17Five 3).toNat

/-- info: 1 -/
#guard_msgs in #eval (HexModArith.ZMod64.pow mod17Typical 0).toNat

/-- info: 3 -/
#guard_msgs in #eval (HexModArith.ZMod64.pow mod16Three 5).toNat

#guard (HexModArith.ZMod64.pow mod17Five 3).toNat = mod17Five.toNat ^ 3 % 17
#guard (HexModArith.ZMod64.pow mod17Typical 0).toNat = mod17Typical.toNat ^ 0 % 17
#guard (HexModArith.ZMod64.pow mod16Three 5).toNat = mod16Three.toNat ^ 5 % 16

end ZMod64
end Conformance
end HexModArith
