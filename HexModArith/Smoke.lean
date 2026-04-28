import HexModArith.Basic

/-!
Executable smoke tests for the default `ZMod64` multiplication path.

Because `Hex.ZMod64.mul` is extern-backed, these checks live in a separate
module so `#eval` runs against the compiled native implementation from
`HexModArith.Basic`.
-/
namespace Hex
namespace ZMod64

instance : Bounds (2 ^ 31 - 1) := ⟨by decide, by decide⟩
instance : Bounds (2 ^ 63 + 29) := ⟨by decide, by decide⟩

private def mersenneA : ZMod64 (2 ^ 31 - 1) := ofNat _ (2 ^ 31 - 2)
private def mersenneB : ZMod64 (2 ^ 31 - 1) := ofNat _ (2 ^ 31 - 3)
private def wideA : ZMod64 (2 ^ 63 + 29) := ofNat _ (2 ^ 63 + 1)
private def wideB : ZMod64 (2 ^ 63 + 29) := ofNat _ (2 ^ 63 - 17)

/-- info: 2 -/
#guard_msgs in #eval (mul mersenneA mersenneB).toNat

/-- info: 1288 -/
#guard_msgs in #eval (mul wideA wideB).toNat

#guard (mul mersenneA mersenneB).toNat = 2
#guard (mul wideA wideB).toNat = 1288

end ZMod64
end Hex
