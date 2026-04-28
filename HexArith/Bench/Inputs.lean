import HexArith.Bench.Random
import HexArith.ExtGcd
import HexArith.PowMod
import HexArith.Barrett.Context
import HexArith.Montgomery.Context

/-!
# HexArith benchmark input generators / runners

One `runX` per family. Each takes a seed plus the family parameter and
returns a `UInt64` hash of the result (used by the driver to verify
that timing variations don't come with output drift).

Inputs are derived deterministically from the seed; the same `(seed, param)`
always yields the same input, which matches the `hyperfine`-style
expectation that repeat runs measure steady-state throughput on the same
work.
-/

namespace HexArith.Bench.Inputs

open HexArith

/-- Return the low 64 bits of a Nat, padded with zeros if smaller. -/
@[inline] def natHash (n : Nat) : UInt64 :=
  (n % (1 <<< 64)).toUInt64

/--
A1 — random coprimality-not-required `Nat.extGcd` on a pair of `bits`-bit
inputs. Hash of `gcd ⊕ s ⊕ t-low` (mod 2^64).
-/
def runA1 (seed : UInt64) (bits : Nat) : UInt64 :=
  let (a, s₁) := Random.nextNonZeroBits seed bits
  let (b, _) := Random.nextNonZeroBits s₁ bits
  let (g, sCoeff, tCoeff) := extGcd a b
  natHash g ^^^ (Int.toNat sCoeff.natAbs).toUInt64 ^^^ (Int.toNat tCoeff.natAbs).toUInt64

/--
A2 — `Nat.powMod` with `bits`-bit base, exponent, and modulus.
-/
def runA2 (seed : UInt64) (bits : Nat) : UInt64 :=
  let (a, s₁) := Random.nextNonZeroBits seed bits
  let (n, s₂) := Random.nextNonZeroBits s₁ bits
  let (p₀, _) := Random.nextNonZeroBits s₂ bits
  -- ensure p > 1 (powMod tolerates p=1 but it gives a degenerate result)
  let p := p₀ + 2
  natHash (powMod a n p)

/-- The committed Barrett modulus for A3 (near-2³² prime, 4294967291 = 2³² − 5). -/
abbrev a3Modulus : UInt64 := 4294967291

/--
A3 — `BarrettCtx.mulMod` throughput: do `n` mulMods at the committed
modulus. The Barrett context is constructed inside the function rather
than at top level — top-level `def`s of structures with proof fields
get eagerly evaluated by the Lean runtime, which deadlocked module
init in earlier versions.
-/
def runA3 (seed : UInt64) (n : Nat) : UInt64 := Id.run do
  let ctx : BarrettCtx a3Modulus := BarrettCtx.mk a3Modulus (by decide) (by decide)
  let (a₀, s₁) := Random.nextRange seed a3Modulus.toNat
  let (b₀, _) := Random.nextRange s₁ a3Modulus.toNat
  let y : UInt64 := b₀.toUInt64
  let mut x : UInt64 := a₀.toUInt64
  for _ in [0:n] do
    x := ctx.mulMod x y
  return x

/--
The committed Montgomery modulus for A4. **Caveat:** the current
`HexArith.MontCtx` scaffolding uses `montgomeryRadixInvNat` inside
`mulMont` / `fromMont`, which is `(List.range p.toNat).find? …` —
brute-force search of `[0, p)`. So any modulus larger than ~10⁶ is
unusable here. We pick 65537 (Fermat prime) as the largest workable
choice for now and document that this is a scaffold limitation, not a
benchmark choice. The HexArith plan to replace `montgomeryRadixInvNat`
with a real Bezout-based inverse will lift this.
-/
abbrev a4Modulus : UInt64 := 65537

/--
A4 — `MontCtx.mulMont` throughput: round-trip `toMont` once, do `n`
`mulMont`s, round-trip `fromMont` once. Ctx constructed inside the
function (see runA3 for why).
-/
def runA4 (seed : UInt64) (n : Nat) : UInt64 := Id.run do
  let ctx : MontCtx a4Modulus := MontCtx.mk a4Modulus (by decide)
  let (a₀, s₁) := Random.nextRange seed (a4Modulus.toNat - 1)
  let (b₀, _) := Random.nextRange s₁ (a4Modulus.toNat - 1)
  let aM := ctx.toMont a₀.toUInt64
  let bM := ctx.toMont b₀.toUInt64
  let mut x : UInt64 := aM
  for _ in [0:n] do
    x := ctx.mulMont x bM
  return ctx.fromMont x

end HexArith.Bench.Inputs
