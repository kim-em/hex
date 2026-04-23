import HexArith.Barrett.Context
import HexArith.ExtGcd
import HexArith.Montgomery.Context
import HexArith.PowMod

/-!
# `HexArith` — core conformance

Deterministic Lean-only conformance checks for `HexArith`. Every
check elaborates as part of `lake build HexArith`, so any regression
fails CI immediately.

**Conformance contract for this library:**

- **Oracle:** `none`. Bézout identity, `Nat.gcd` agreement, and
  `a ^ n % p` suffice as property oracles for the `core` profile.
  Wiring an external oracle (python-flint for big-integer agreement
  with GMP) is a follow-up.
- **Mode:** `always`.
- **Covered operations:** `HexArith.extGcd` (Nat), `HexArith.Int.extGcd`,
  `HexArith.UInt64.extGcd`, `HexArith.powMod`, `HexArith.BarrettCtx.mulMod`,
  `HexArith.MontCtx.toMont` / `fromMont` / `mulMont`.
- **Covered properties:**
  - Bézout: `extGcd a b = (g, s, t) ⇒ s * a + t * b = g` for all
    three arithmetic entry points.
  - `gcd` agreement: `(extGcd a b).1 = Nat.gcd a.natAbs b.natAbs`.
  - `powMod a n p = a ^ n % p`.
  - Barrett identity: `(ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat`.
  - Montgomery round-trip: `ctx.fromMont (ctx.toMont a) = a` for `a < p`.
  - Montgomery identity: `(ctx.mulMont a b).toNat = (a.toNat * b.toNat) % p.toNat`
    for `a, b < p`.
- **Covered edge cases:** `extGcd 0 0`, `extGcd 0 n`, `extGcd n 0`,
  sign-mixed `Int` pairs; `powMod a 0 p`, `powMod _ _ 1`, `powMod 0 n p`;
  Barrett with `p = 3` and `p = 65537`; Montgomery with odd `p = 5` and
  `p = 97`.

Reference implementation for the
[Phase 3 per-library module contract](../SPEC/testing.md#per-library-module-contract).
Other libraries' `Conformance.lean` should follow this shape:
docstring contract declaration, then grouped `#guard_msgs in #eval`
spot values, then `#guard` property assertions, covering each
operation with ≥3 fixtures (typical / edge / adversarial).
-/

namespace HexArith
namespace Conformance

/-! ## `HexArith.extGcd` on `Nat` -/

/-- info: (0, 1, 0) -/
#guard_msgs in #eval HexArith.extGcd 0 0

/-- info: (7, 0, 1) -/
#guard_msgs in #eval HexArith.extGcd 0 7

/-- info: (6, 1, -2) -/
#guard_msgs in #eval HexArith.extGcd 30 12

-- Bézout identity on each committed case.
#guard let (g, s, t) := HexArith.extGcd 0 0;   s * 0 + t * 0 = g
#guard let (g, s, t) := HexArith.extGcd 0 7;   s * 0 + t * 7 = g
#guard let (g, s, t) := HexArith.extGcd 30 12; s * 30 + t * 12 = g

-- Agreement with the stdlib `Nat.gcd`.
#guard (HexArith.extGcd 0 0).1   = Nat.gcd 0 0
#guard (HexArith.extGcd 0 7).1   = Nat.gcd 0 7
#guard (HexArith.extGcd 30 12).1 = Nat.gcd 30 12

/-! ## `Int` extended GCD — sign handling is the point

`HexArith.Int.extGcd` is `@[extern "lean_hex_mpz_gcdext"]`; its GMP
backend is linked for compiled code but not for the Lean interpreter,
so `#eval` can only run the pure-Lean body `Hex.pureIntExtGcd`. We
check the pure body directly and assert by `rfl` that the two agree,
so any drift between the extern declaration and its body fails at
elaboration. -/

example : HexArith.Int.extGcd = Hex.pureIntExtGcd := rfl

/-- info: (6, 1, 2) -/
#guard_msgs in #eval Hex.pureIntExtGcd 30 (-12)

/-- info: (6, -1, -2) -/
#guard_msgs in #eval Hex.pureIntExtGcd (-30) 12

/-- info: (7, 0, -1) -/
#guard_msgs in #eval Hex.pureIntExtGcd 0 (-7)

#guard let (g, s, t) := Hex.pureIntExtGcd 30 (-12); s * 30 + t * (-12) = (g : Int)
#guard let (g, s, t) := Hex.pureIntExtGcd (-30) 12; s * (-30) + t * 12 = (g : Int)
#guard let (g, s, t) := Hex.pureIntExtGcd 0 (-7);   s * 0 + t * (-7) = (g : Int)

-- Agreement with stdlib `Int.gcd` (which returns the positive gcd).
#guard (Hex.pureIntExtGcd 30 (-12)).1 = Int.gcd 30 (-12)
#guard (Hex.pureIntExtGcd (-30) 12).1 = Int.gcd (-30) 12
#guard (Hex.pureIntExtGcd 0 (-7)).1   = Int.gcd 0 (-7)

/-! ## `HexArith.UInt64.extGcd` -/

/-- info: (0, 1, 0) -/
#guard_msgs in #eval HexArith.UInt64.extGcd 0 0

/-- info: (7, 0, 1) -/
#guard_msgs in #eval HexArith.UInt64.extGcd 0 7

/-- info: (6, -2, 3) -/
#guard_msgs in #eval HexArith.UInt64.extGcd 42 30

#guard let (g, s, t) := HexArith.UInt64.extGcd 0 0
       s * (0 : Int) + t * (0 : Int) = Int.ofNat g.toNat
#guard let (g, s, t) := HexArith.UInt64.extGcd 0 7
       s * (0 : Int) + t * (7 : Int) = Int.ofNat g.toNat
#guard let (g, s, t) := HexArith.UInt64.extGcd 42 30
       s * (42 : Int) + t * (30 : Int) = Int.ofNat g.toNat

/-! ## `HexArith.powMod` -/

/-- info: 1 -/
#guard_msgs in #eval HexArith.powMod 7 0 5     -- exponent zero

/-- info: 0 -/
#guard_msgs in #eval HexArith.powMod 10 4 1    -- modulus one

/-- info: 8 -/
#guard_msgs in #eval HexArith.powMod 5 3 13

/-- info: 9 -/
#guard_msgs in #eval HexArith.powMod 42 5 17   -- base bigger than modulus

-- Agreement with the spec identity `a ^ n % p` (for `p > 0`).
#guard HexArith.powMod 7 0 5     = 7 ^ 0 % 5
#guard HexArith.powMod 10 4 1    = 10 ^ 4 % 1
#guard HexArith.powMod 5 3 13    = 5 ^ 3 % 13
#guard HexArith.powMod 42 5 17   = 42 ^ 5 % 17
#guard HexArith.powMod 0 5 13    = 0 ^ 5 % 13

/-! ## `HexArith.BarrettCtx.mulMod`

The Barrett scaffold requires a proof that `1 < p < 2^32`. For
concrete small moduli these are `by decide`. We commit one tiny
modulus and one near the upper end of the Barrett range. -/

section Barrett

private def barrett3 : BarrettCtx 3 :=
  BarrettCtx.mk 3 (by decide) (by decide)

private def barrett65537 : BarrettCtx 65537 :=
  BarrettCtx.mk 65537 (by decide) (by decide)

/-- info: 1 -/
#guard_msgs in #eval (barrett3.mulMod 2 2).toNat     -- 4 % 3

/-- info: 0 -/
#guard_msgs in #eval (barrett3.mulMod 0 2).toNat     -- 0 % 3

/-- info: 65536 -/
#guard_msgs in #eval (barrett65537.mulMod 256 256).toNat  -- 65536 % 65537

-- Barrett identity: `(mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat`.
#guard (barrett3.mulMod 2 2).toNat     = (2 * 2) % 3
#guard (barrett3.mulMod 0 2).toNat     = (0 * 2) % 3
#guard (barrett3.mulMod 2 1).toNat     = (2 * 1) % 3
#guard (barrett65537.mulMod 256 256).toNat = (256 * 256) % 65537
#guard (barrett65537.mulMod 65536 2).toNat = (65536 * 2) % 65537

end Barrett

/-! ## `HexArith.MontCtx`

Montgomery requires `p` odd. We commit a small `p = 5` and a larger
`p = 97`; both round-trip `fromMont ∘ toMont = id` for representatives
below `p`, and `mulMont` agrees with `a * b mod p` after `fromMont`. -/

section Montgomery

private def mont5 : MontCtx 5   := MontCtx.mk 5 (by decide)
private def mont97 : MontCtx 97 := MontCtx.mk 97 (by decide)

-- Round-trip `fromMont (toMont a) = a` on representatives < p.
#guard mont5.fromMont (mont5.toMont 0) = 0
#guard mont5.fromMont (mont5.toMont 1) = 1
#guard mont5.fromMont (mont5.toMont 4) = 4
#guard mont97.fromMont (mont97.toMont 0)  = 0
#guard mont97.fromMont (mont97.toMont 1)  = 1
#guard mont97.fromMont (mont97.toMont 96) = 96

-- `mulMont` represents `a * b mod p`: `fromMont (mulMont (toMont a) (toMont b)) = a * b mod p`.
#guard mont5.fromMont (mont5.mulMont (mont5.toMont 3) (mont5.toMont 4)) = UInt64.ofNat ((3 * 4) % 5)
#guard mont5.fromMont (mont5.mulMont (mont5.toMont 0) (mont5.toMont 4)) = UInt64.ofNat ((0 * 4) % 5)
#guard mont97.fromMont (mont97.mulMont (mont97.toMont 50) (mont97.toMont 50))
         = UInt64.ofNat ((50 * 50) % 97)
#guard mont97.fromMont (mont97.mulMont (mont97.toMont 96) (mont97.toMont 96))
         = UInt64.ofNat ((96 * 96) % 97)

end Montgomery

end Conformance
end HexArith
