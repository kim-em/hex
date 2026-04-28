import HexLLL.Bench.Random
import HexLLL.Loop
import HexMatrix

/-!
# HexLLL benchmark input generators

Because `lll` has `n : Nat` in the type, we can't dispatch on a runtime
`n`. Instead we enumerate a small discrete ladder of dimensions
`{4, 6, 8, 12, 16, 20, 24}` and dispatch the runner by pattern match.
Dimensions outside the ladder snap to the nearest supported value.

Inputs are generated deterministically from a `(seed, dim, bits)`
triple using SplitMix64 from [Random.lean](./Random.lean).
-/

namespace HexLLL.Bench.Inputs

open HexMatrix HexLLL

/-- Generate an `n × n` Int matrix with entries uniformly drawn in
`[-(2^bits), 2^bits]`. Uses a monadic SplitMix64 unfold; same seed →
same matrix. -/
def uniformIntMatrix (n : Nat) (bits : Nat) (seed : UInt64) : Matrix Int n n := Id.run do
  let mut state := seed
  let mut rows : Array (Vector Int n) := Array.mkEmpty n
  for _ in [0:n] do
    let mut row : Array Int := Array.mkEmpty n
    for _ in [0:n] do
      let (v, s') := Random.nextSignedBits state bits
      state := s'
      row := row.push v
    rows := rows.push (Vector.ofFn fun i => row[i.1]!)
  return Vector.ofFn fun i => rows[i.1]!

/-- A monoidal hash of a matrix: XOR the low-64 bits of each entry. -/
def hashMatrix (M : Matrix Int n n) : UInt64 :=
  M.toList.foldl (init := 0) fun acc row =>
    row.toList.foldl (init := acc) fun acc' entry =>
      acc' ^^^ (Int.natAbs entry % (1 <<< 64)).toUInt64

/-- The `independent` predicate decomposes to per-row positivity of leading
Gram determinants — each is `0 < Int`, decidable. Lean doesn't synthesize
this automatically because the `gramDet` definitions are wrapped, so we
make the instance explicit. -/
instance Matrix.decidableIndependent {n m : Nat} (b : Matrix Int n m) :
    Decidable b.independent := by
  unfold Matrix.independent
  exact inferInstance

/--
One LLL run at statically known dimension `n`, given a matrix `b`.
`hn : 1 ≤ n` is supplied by the caller. Independence is checked at
runtime via the explicit `Decidable` instance above; degenerate
samples (very rare for random large-entry inputs) return 0.
-/
def runLllAt (n : Nat) (hn : 1 ≤ n) (b : Matrix Int n n) : UInt64 :=
  if h : b.independent then
    hashMatrix (lll b (3/4) (by decide +kernel) (by decide +kernel) hn h)
  else
    0

/-- L1: square uniform random at a given dim. Entry bit-width fixed at 20. -/
def runL1AtDim (n : Nat) (hn : 1 ≤ n) (seed : UInt64) : UInt64 :=
  runLllAt n hn (uniformIntMatrix n 20 seed)

/-- L2: arith-heavy; fixed dim, sweep entry bit-width. Plan picked
n=20; with the current naive swap-step that already costs seconds even
at tiny bit-widths. For the prototype we drop to n=6 so we can actually
sweep B, at the cost of making the arith-vs-swap distinction less sharp.
This is a known simplification — see progress retrospective. -/
def runL2AtBits (bits : Nat) (seed : UInt64) : UInt64 :=
  runLllAt 6 (by decide) (uniformIntMatrix 6 bits seed)

/-- Snap an arbitrary dim to the supported ladder. -/
def snapL1Dim (n : Nat) : Nat :=
  if n ≤ 4 then 4
  else if n ≤ 6 then 6
  else if n ≤ 8 then 8
  else if n ≤ 12 then 12
  else if n ≤ 16 then 16
  else if n ≤ 20 then 20
  else 24

/-- Dispatch `runL1` by snapped dim. Unsupported dims fall through to 24. -/
def runL1 (seed : UInt64) (n : Nat) : UInt64 :=
  match snapL1Dim n with
  |  4 => runL1AtDim  4 (by decide) seed
  |  6 => runL1AtDim  6 (by decide) seed
  |  8 => runL1AtDim  8 (by decide) seed
  | 12 => runL1AtDim 12 (by decide) seed
  | 16 => runL1AtDim 16 (by decide) seed
  | 20 => runL1AtDim 20 (by decide) seed
  | _  => runL1AtDim 24 (by decide) seed

/-- Dispatch `runL2` at fixed dim, varying bits. -/
def runL2 (seed : UInt64) (bits : Nat) : UInt64 :=
  runL2AtBits bits seed

end HexLLL.Bench.Inputs
