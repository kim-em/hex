import HexModArithMathlib.ZMod64

/-!
# `HexModArithMathlib` — core conformance

Deterministic Lean-only conformance checks for the bridge between
`HexModArith.ZMod64 p` and Mathlib's `ZMod p`.

**Conformance contract for this slice:**

- **Oracle:** `none`. This bridge library uses internal equivalence and
  representative checks on committed residues rather than an external
  oracle.
- **Mode:** `always`.
- **Covered operations:** `HexModArithMathlib.ZMod64.toZMod`,
  `HexModArithMathlib.ZMod64.ofZMod`.
- **Covered properties:**
  - the bridge round-trips both from executable residues to Mathlib and
    back on committed moduli;
  - the chosen Mathlib representative agrees with the executable
    `toNat` view on committed residues;
  - `toZMod` preserves natural and integer casts on committed inputs.
- **Covered edge cases:** modulus `1`, zero residue, negative integer
  casts, and representatives at `p - 1`.
-/

namespace HexModArithMathlib
namespace Conformance

open HexModArith
open HexModArithMathlib.ZMod64

namespace ZMod64

private def z1 (n : Nat) : HexModArith.ZMod64 1 :=
  HexModArith.ZMod64.ofNat 1 n (by decide)

private def z17 (n : Nat) : HexModArith.ZMod64 17 :=
  HexModArith.ZMod64.ofNat 17 n (by decide)

private def z97 (n : Nat) : HexModArith.ZMod64 97 :=
  HexModArith.ZMod64.ofNat 97 n (by decide)

/-! ## `ZMod64.toZMod` -/

/-- info: 3 -/
#guard_msgs in #eval representative (toZMod (z17 20))

/-- info: 0 -/
#guard_msgs in #eval representative (toZMod (z1 7))

/-- info: 96 -/
#guard_msgs in #eval representative (toZMod (z97 96))

#guard toZMod (z17 20) = (20 : ZMod 17)
#guard representative (toZMod (z1 7)) = 0
#guard toZMod (z97 96) = (96 : ZMod 97)

/-! ## `ZMod64.ofZMod` -/

/-- info: 3 -/
#guard_msgs in #eval (ofZMod (20 : ZMod 17)).toNat

/-- info: 0 -/
#guard_msgs in #eval (ofZMod (7 : ZMod 1)).toNat

/-- info: 96 -/
#guard_msgs in #eval (ofZMod (-1 : ZMod 97)).toNat

#guard (ofZMod (20 : ZMod 17)).toNat = 3
#guard (ofZMod (7 : ZMod 1)).toNat = 0
#guard (ofZMod (-1 : ZMod 97)).toNat = 96

/-! ## Round-trip identities -/

#guard (ofZMod (toZMod (z17 20))).toNat = (z17 20).toNat
#guard (ofZMod (toZMod (z1 7))).toNat = (z1 7).toNat
#guard toZMod (ofZMod (-3 : ZMod 17)) = (-3 : ZMod 17)
#guard toZMod (ofZMod (96 : ZMod 97)) = (96 : ZMod 97)

/-! ## Representative preservation -/

#guard representative (toZMod (z17 20)) = (z17 20).toNat
#guard representative (toZMod (z1 7)) = (z1 7).toNat
#guard (ofZMod (96 : ZMod 97)).toNat = representative (96 : ZMod 97)
#guard (ofZMod (-3 : ZMod 17)).toNat = representative (-3 : ZMod 17)

/-! ## Cast transport -/

#guard toZMod (20 : HexModArith.ZMod64 17) = (20 : ZMod 17)
#guard toZMod (0 : HexModArith.ZMod64 1) = (0 : ZMod 1)
#guard toZMod (-3 : HexModArith.ZMod64 17) = (-3 : ZMod 17)
#guard toZMod (-98 : HexModArith.ZMod64 97) = (-98 : ZMod 97)

end ZMod64

end Conformance
end HexModArithMathlib
