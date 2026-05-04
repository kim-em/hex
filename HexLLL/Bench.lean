import HexLLL
import Init.Data.Rat.Lemmas
import LeanBench

/-!
Benchmark registrations for `hex-lll`.

This first Phase 4 slice covers the executable `LLLState` operations. Fixture
construction builds the integer Gram-Schmidt state once in `prep`; the timed
targets measure the state update or projection surfaces and return compact
checksums of the affected cells.

Scientific registrations:

* `runSizeReduceColumnChecksum`: one targeted column reduction against the
  previous row of a prepared `(n + 3) x (2(n + 3) + 1)` state, wrapped in a
  fixed hot loop for signal-floor stability.
* `runSizeReduceChecksum`: full reduction of the final prepared row.
* `runSwapStepChecksum`: one adjacent swap at the final prepared row, wrapped
  in a fixed hot loop for signal-floor stability.
* `runGramSchmidtCoeffChecksum`: rational coefficient recovery from stored
  integer `ν` and `d`, wrapped in a fixed hot loop for signal-floor stability.
* `runPotential`: prefix product of the stored Gram determinants, wrapped in a
  fixed hot loop for signal-floor stability.
* `runFirstShortVectorChecksum`: the public BZ-facing LLL recombination entry
  point, with fixture construction and independence checking hoisted into
  `prep`.
-/

namespace Hex.LLLBench

/-- Row-major deterministic fixture for one integer basis. -/
structure IntBasisInput where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Prepared `LLLState` plus stable indices used by the benchmark targets. -/
structure StateInput where
  rows : Nat
  cols : Nat
  state : LLLState rows cols
  j : Fin rows
  k : Fin rows
  hjk : j.val < k.val

instance : Hashable StateInput where
  hash input :=
    hash (input.rows, input.cols, input.j.val, input.k.val)

/-- Prepared public `lll` input. The valid case stores the independence witness
computed during `prep`; the invalid case keeps registration total if a future
fixture change accidentally loses full rank. -/
inductive PublicLLLInput where
  | valid (rows cols : Nat) (basis : Matrix Int rows cols)
      (hn : 1 ≤ rows) (hind : basis.independent)
  | invalid

instance : Hashable PublicLLLInput where
  hash
    | .valid rows cols _ _ _ => hash (rows, cols, true)
    | .invalid => hash false

/-- Deterministic small integer entry generator keyed by shape and position.
The diagonal offset keeps the prepared bases independent in the benchmark
range while still giving size-reduction and swap updates nontrivial data. -/
def entryValue (rows cols row col salt : Nat) : Int :=
  let raw :=
    ((row + 1) * 37 +
      (col + 3) * 29 +
      (rows + 5) * 17 +
      (cols + 7) * 13 +
      salt) % 5
  let centered := Int.ofNat raw - 2
  if row = col then centered + Int.ofNat (rows + 3) else centered

/-- Deterministic row-major matrix fixture of shape `rows x cols`. -/
def flatBasis (rows cols salt : Nat) : Array Int :=
  if rows = 0 || cols = 0 then
    #[]
  else
    (Array.range (rows * cols)).map fun idx =>
      let row := idx / cols
      let col := idx % cols
      entryValue rows cols row col salt

/-- Reconstruct a typed dense matrix from row-major entries. -/
def matrixOfFlat (input : IntBasisInput) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

/-- Executable independence predicate used only during benchmark preparation. -/
def independentCheck (b : Matrix Int n m) : Bool :=
  (List.finRange n).all fun k =>
    0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) k)

private theorem independent_of_independentCheck_eq_true
    {b : Matrix Int n m} (h : independentCheck b = true) : b.independent := by
  simpa [Matrix.independent, independentCheck] using h

private theorem quarter_lt_threeQuarter : (1 / 4 : Rat) < 3 / 4 := by
  grind

private theorem threeQuarter_le_one : (3 / 4 : Rat) ≤ 1 := by
  grind

/-- Build the certified executable LLL state for a deterministic matrix. -/
def stateOf (b : Matrix Int n m) : LLLState n m where
  b := b
  ν := GramSchmidt.Int.scaledCoeffs b
  d := GramSchmidt.Int.gramDetVec b
  ν_eq := by
    intro i j hi hj hji
    rw [GramSchmidt.Int.gramDetVec_eq_gramDet b (j + 1)
      (Nat.succ_le_of_lt (Nat.lt_trans hji hi))]
    simpa [GramSchmidt.entry, Matrix.row] using
      (GramSchmidt.Int.scaledCoeffs_eq b i j hi hji)
  d_eq := by
    intro i hi
    exact GramSchmidt.Int.gramDetVec_eq_gramDet b i (Nat.le_of_lt_succ hi)

/-- Per-parameter fixture: a prepared `(n + 3) x (2(n + 3) + 1)` LLL state. -/
def prepStateInput (n : Nat) : StateInput :=
  let rows := n + 3
  let cols := 2 * rows + 1
  let flat : IntBasisInput :=
    { rows := rows
      cols := cols
      entries := flatBasis rows cols 197 }
  let j : Fin rows := ⟨n + 1, by simp [rows]⟩
  let k : Fin rows := ⟨n + 2, by simp [rows]⟩
  { rows := rows
    cols := cols
    state := stateOf (matrixOfFlat flat)
    j := j
    k := k
    hjk := by
      change n + 1 < n + 2
      omega }

/-- Per-parameter public LLL fixture: a BZ-shaped integer basis with one row per
synthetic lifted factor and one coefficient column per ambient lattice
coordinate. The independence decision is intentionally hoisted out of the timed
body. -/
def prepPublicLLLInput (n : Nat) : PublicLLLInput :=
  let rows := n + 3
  let cols := 2 * rows + 1
  let flat : IntBasisInput :=
    { rows := rows
      cols := cols
      entries := flatBasis rows cols 313 }
  let basis := matrixOfFlat flat
  if hcheck : independentCheck basis then
    .valid rows cols basis (by simp [rows])
      (independent_of_independentCheck_eq_true (by simpa using hcheck))
  else
    .invalid

/-- Stable checksum for integer vectors. -/
def intVectorChecksum (v : Vector Int n) : Int :=
  (List.finRange n).foldl
    (fun acc i => acc * 65_537 + v[i])
    0

/-- Stable checksum for natural vectors. -/
def natVectorChecksum (v : Vector Nat n) : Nat :=
  (List.finRange n).foldl
    (fun acc i => acc * 65_537 + v[i])
    0

/-- Stable checksum for two integer rows. -/
def intRowPairChecksum (M : Matrix Int n m) (i j : Fin n) : Int :=
  intVectorChecksum (M.row i) * 65_537 + intVectorChecksum (M.row j)

/-- Stable checksum for one row of the stored scaled-coefficient matrix. -/
def coeffRowChecksum (M : Matrix Int n n) (i : Fin n) : Int :=
  intVectorChecksum (M.row i)

/-- Stable checksum for a state update's affected row and determinant data. -/
def stateUpdateChecksum (s : LLLState n m) (i j : Fin n) : Int :=
  intRowPairChecksum s.b i j * 65_537 +
    coeffRowChecksum s.ν i * 257 +
    coeffRowChecksum s.ν j +
    Int.ofNat (natVectorChecksum s.d)

/-- Model for reducing one row against one previous row: one basis row update
over `m = 2(n + 3) + 1` columns plus the affected coefficient prefix. -/
def sizeReduceColumnComplexity (n : Nat) : Nat :=
  (2 * (n + 3) + 1) + n + 3

/-- Model for reducing the final row against all earlier rows: `k` row updates
over `m` columns plus the triangular coefficient-prefix updates. -/
def sizeReduceComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * (2 * rows + 1) + rows * rows

/-- Model for an adjacent swap update: one basis swap over `m` columns, one
determinant write, and linear coefficient updates in the affected rows/columns. -/
def swapStepComplexity (n : Nat) : Nat :=
  (2 * (n + 3) + 1) + n + 3

/-- Model for one stored rational coefficient projection. -/
def gramSchmidtCoeffComplexity (_n : Nat) : Nat :=
  1

/-- Model for multiplying the determinant prefix `d_1, ..., d_{rows-1}` with
determinant bit-width growth from the prepared integer fixture. -/
def potentialComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * rows * rows

/-- Model for public LLL recombination on the prepared `rows x (2 rows + 1)`
fixture. The timed call includes `LLLState.ofBasis`'s integer Gram surface,
followed by a no-backtracking LLL pass on this diagonal-dominant family and a
linear checksum of the first reduced row. -/
def firstShortVectorComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * rows * rows + rows * rows * (2 * rows + 1)

/-- Fixed repeat count for one-step linear state updates. This is independent
of `n`, so it changes only the constant factor in the declared linear model. -/
def stateStepHotRepeats : Nat := 2048

/-- Fixed repeat count for full row reduction. This is independent of `n`, so
it changes only the constant factor in the declared quadratic model. -/
def sizeReduceHotRepeats : Nat := 2048

/-- Fixed repeat count for one stored coefficient projection. This is
independent of `n`, so it changes only the constant factor in the declared
constant model. -/
def gramSchmidtCoeffHotRepeats : Nat := 65536

/-- Fixed repeat count for determinant-prefix products. This is independent of
`n`, so it changes only the constant factor in the declared linear model. -/
def potentialHotRepeats : Nat := 128

/-- Fixed repeat count for the public LLL recombination surface. This is
independent of `n`, so it changes only the constant factor in the declared
Gram-surface-plus-loop model. -/
def firstShortVectorHotRepeats : Nat := 8

/-- Repeat a deterministic integer-valued target with a rolling checksum. -/
def repeatIntChecksum (repeats : Nat) (f : Unit → Int) : Int :=
  (List.range repeats).foldl
    (fun acc _ => acc * 65_537 + f ())
    0

/-- Repeat a deterministic natural-valued target with a rolling checksum. -/
def repeatNatChecksum (repeats : Nat) (f : Unit → Nat) : Nat :=
  (List.range repeats).foldl
    (fun acc _ => acc * 65_537 + f ())
    0

/-- Benchmark target: one targeted size-reduction step. -/
def runSizeReduceColumnChecksum (input : StateInput) : Int :=
  repeatIntChecksum stateStepHotRepeats fun _ =>
    let s' := input.state.sizeReduceColumn input.j input.k input.hjk
    stateUpdateChecksum s' input.j input.k

/-- Benchmark target: full size reduction of the prepared final row. -/
def runSizeReduceChecksum (input : StateInput) : Int :=
  repeatIntChecksum sizeReduceHotRepeats fun _ =>
    let s' := input.state.sizeReduce input.k.val
    stateUpdateChecksum s' input.j input.k

/-- Benchmark target: adjacent swap at the prepared final row. -/
def runSwapStepChecksum (input : StateInput) : Int :=
  repeatIntChecksum stateStepHotRepeats fun _ =>
    let s' := input.state.swapStep input.k.val
    stateUpdateChecksum s' input.j input.k

/-- Benchmark target: recover one rational Gram-Schmidt coefficient from the
stored integer state and checksum its normalized numerator and denominator.
This is the computable body of `LLLState.gramSchmidtCoeff`; the public
projection is marked `noncomputable` for proof-layer signalling and cannot be
used directly as an executable benchmark target. -/
def runGramSchmidtCoeffChecksum (input : StateInput) : Int :=
  repeatIntChecksum gramSchmidtCoeffHotRepeats fun _ =>
    let q :=
      (((input.state.ν.get input.k).get input.j : Int) : Rat) /
        (input.state.d.get
          ⟨input.j.val + 1, Nat.succ_lt_succ input.j.isLt⟩ : Rat)
    q.num * 65_537 + Int.ofNat q.den

/-- Benchmark target: compute the LLL termination potential. -/
def runPotential (input : StateInput) : Nat :=
  repeatNatChecksum potentialHotRepeats fun _ =>
    input.state.potential

/-- Benchmark target: run the public downstream short-vector entry point and
checksum the reduced first row. -/
def runFirstShortVectorChecksum : PublicLLLInput → Int
  | .valid _ _ basis hn hind =>
      repeatIntChecksum firstShortVectorHotRepeats fun _ =>
        intVectorChecksum
          (lll.firstShortVector basis (3 / 4 : Rat)
            quarter_lt_threeQuarter threeQuarter_le_one hn hind)
  | .invalid => 0

/- Complexity derivation: `prepStateInput n` gives `rows = n + 3` and
`cols = 2 * (n + 3) + 1`. A single targeted reduction updates one basis row
over `cols` entries and one coefficient prefix bounded by `rows`; the fixed
hot-loop repeat count is independent of `n`. -/
setup_benchmark runSizeReduceColumnChecksum n => sizeReduceColumnComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 96
    paramCeiling := 160
    paramSchedule := .custom #[96, 128, 160]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

/- Complexity derivation: full size reduction of the final prepared row
performs one targeted row update for each earlier row, so the model is
`rows * cols` for basis entries plus the triangular coefficient-prefix surface,
bounded here by `rows^2`; the fixed hot-loop repeat count is independent of
`n`. -/
setup_benchmark runSizeReduceChecksum n => sizeReduceComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 80
    paramCeiling := 144
    paramSchedule := .custom #[80, 96, 112, 128, 144]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
  }

/- Complexity derivation: an adjacent swap exchanges two basis rows over
`cols` entries, rewrites one determinant, swaps the lower coefficient prefix,
and updates the two affected coefficient columns for rows above the pivot; all
terms are linear in rows, and the fixed hot-loop repeat count is independent of
`n`. -/
setup_benchmark runSwapStepChecksum n => swapStepComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 96
    paramCeiling := 160
    paramSchedule := .custom #[96, 128, 160]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

/- Complexity derivation: `gramSchmidtCoeff` reads one stored `ν[k][j]` entry
and one stored `d[j+1]` denominator, then performs a single rational division;
the fixed hot-loop repeat count is independent of `n`. -/
setup_benchmark runGramSchmidtCoeffChecksum n => gramSchmidtCoeffComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 32
    paramCeiling := 128
    paramSchedule := .custom #[32, 64, 96, 128]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

/- Complexity derivation: `potential` folds once over the prepared state's
determinant prefix. The fixture has `rows = n + 3`, so the prefix length is
`n + 2`; each stored Gram determinant has row-dependent bit width, and the
running product's bit width grows across the prefix. The resulting executable
integer-arithmetic surface is cubic in `rows`; the fixed hot-loop repeat count
is independent of `n`. -/
setup_benchmark runPotential n => potentialComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 192
    paramCeiling := 224
    paramSchedule := .custom #[192, 208, 224]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 200000000
  }

/- Complexity derivation: `lll.firstShortVector` calls the public `lll`
surface, so the timed body builds the initial integer state from the basis,
runs the LLL loop, and reads the first reduced row. On this BZ-shaped
diagonal-dominant fixture the loop performs the linear advance schedule without
backtracking; the dominant intended surface is the same shared integer Gram
construction used by `LLLState.ofBasis`, with the fixed hot-loop repeat count
independent of `n`. -/
setup_benchmark runFirstShortVectorChecksum n => firstShortVectorComplexity n
  with prep := prepPublicLLLInput
  where {
    paramFloor := 5
    paramCeiling := 7
    paramSchedule := .custom #[5, 6, 7]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 600000000
  }

end Hex.LLLBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
