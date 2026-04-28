/-!
# SplitMix64 PRNG for benchmark inputs

A tiny deterministic PRNG used by the HexArith benchmark harness to
generate seed-stable inputs. Duplicated (intentionally, for prototype)
in [HexLLL/Bench/Random.lean](../../HexLLL/Bench/Random.lean) with an
identical API.

The algorithm is Vigna's SplitMix64; see
<https://prng.di.unimi.it/splitmix64.c>. UInt64 arithmetic in Lean 4
wraps, which matches the C reference exactly.
-/

namespace HexLLL.Bench.Random

/-- Advance the SplitMix64 state and return `(out, newState)`. -/
@[inline] def next (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9E3779B97F4A7C15
  let z₁ := s'
  let z₂ := (z₁ ^^^ (z₁ >>> 30)) * 0xBF58476D1CE4E5B9
  let z₃ := (z₂ ^^^ (z₂ >>> 27)) * 0x94D049BB133111EB
  let z₄ := z₃ ^^^ (z₃ >>> 31)
  (z₄, s')

/-- Draw a Nat in `[0, n)` from the PRNG. Uniform up to a tiny modulo bias. -/
@[inline] def nextRange (s : UInt64) (n : Nat) : Nat × UInt64 :=
  let (z, s') := next s
  (z.toNat % n, s')

/-- Draw a Nat with up to `bits` random bits (i.e. in `[0, 2^bits)`). -/
def nextBits (s : UInt64) (bits : Nat) : Nat × UInt64 := Id.run do
  if bits = 0 then return (0, s)
  let mut st := s
  let mut acc : Nat := 0
  let numChunks := (bits + 63) / 64
  for _ in [0:numChunks] do
    let (z, st') := next st
    st := st'
    acc := (acc <<< 64) ||| z.toNat
  let totalBits := numChunks * 64
  if totalBits > bits then
    acc := acc >>> (totalBits - bits)
  return (acc, st)

/--
Draw a non-zero Nat with `bits` random bits, retrying on zero. Used
for benchmark inputs where zero would trivialise the workload.
-/
def nextNonZeroBits (s : UInt64) (bits : Nat) : Nat × UInt64 :=
  let (n, s') := nextBits s bits
  if n = 0 then (1, s') else (n, s')

/--
Draw an Int in `[-2^bits, 2^bits]` (inclusive). The harness uses this
for signed-coefficient inputs in HexLLL; HexArith does not need it but
the API is shared for future deduplication.
-/
def nextSignedBits (s : UInt64) (bits : Nat) : Int × UInt64 :=
  let (n, s') := nextBits s (bits + 1)
  let sign := n &&& 1
  let mag := n >>> 1
  if sign = 0 then (Int.ofNat mag, s') else (-(Int.ofNat mag), s')

end HexLLL.Bench.Random
