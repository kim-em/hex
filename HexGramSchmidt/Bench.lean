import HexGramSchmidt
import LeanBench

/-!
Benchmark registrations for `hex-gram-schmidt`.

This Phase 4 slice measures the executable integer determinant and
row-operation update-helper surfaces. Matrix fixture construction is hoisted
through `prep`; each matrix-valued timed target returns a compact checksum
instead of the full vector or matrix value.

Scientific registrations:

* `runGramDetVecChecksum`: one Bareiss pass over the Gram matrix, with model
  `O(n^3 + n^2*m)` on deterministic `n x (2n + 1)` integer inputs.
* `runScaledCoeffsChecksum`: the full scaled-coefficient matrix surface, using
  the determinant formula for each lower-triangular entry.
* `runSizeReduceChecksum` and `runAdjacentSwapChecksum`: executable row-update
  matrix helpers, checking only affected rows. These wrap a fixed hot loop so
  the timed call clears the child-process signal floor without changing the
  asymptotic model.
* `runAdjacentSwapDenom`: the exact-swap denominator `d[k]`.
* `runAdjacentSwapPivotCoeff`: the scaled pivot coefficient `nu[k][k-1]`.
* `runAdjacentSwapGramDetNumerator` and
  `runAdjacentSwapGramDetQuotient`: the adjacent-swap Gram-determinant update
  helpers.
* `runAdjacentSwapScaledCoeffAbovePrevNumerator` and
  `runAdjacentSwapScaledCoeffAboveCurrNumerator`: the two above-row
  scaled-coefficient numerator helpers.

This file intentionally avoids the noncomputable rational `basis` and `coeffs`
APIs.
-/

namespace Hex.GramSchmidtBench

/-- Flattened benchmark input for one integer basis matrix. -/
structure IntBasisInput where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Prepared typed matrix plus stable row indices for update-helper
benchmarks. `prepUpdateInput n` uses `n + 3` rows so the adjacent-swap
benchmarks always have a previous row and an above-row sample. -/
structure UpdateInput where
  rows : Nat
  cols : Nat
  matrix : Matrix Int rows cols
  sizeReduceSrc : Fin rows
  pivotK : Fin rows
  pivotHK : 0 < pivotK.val
  aboveK : Fin rows
  aboveHK : 0 < aboveK.val
  aboveI : Fin rows
  coeff : Int

instance : Hashable UpdateInput where
  hash input :=
    hash (input.rows, input.cols, input.sizeReduceSrc.val, input.pivotK.val,
      input.aboveK.val, input.aboveI.val, input.coeff)

/-- Deterministic small integer entry generator keyed by shape and position. -/
def entryValue (rows cols row col salt : Nat) : Int :=
  let raw :=
    ((row + 1) * 1_103 +
      (col + 3) * 811 +
      (rows + 5) * 97 +
      (cols + 7) * 53 +
      salt) % 31
  Int.ofNat raw - 15

/-- Smaller deterministic entries for update-helper fixtures. The exact
determinant helpers are meant to measure the row-operation formulas; keeping
entries in `{-1, 0, 1}` avoids spending the whole schedule on coefficient
growth from the synthetic fixture. -/
def updateEntryValue (rows cols row col salt : Nat) : Int :=
  let raw :=
    ((row + 1) * 17 +
      (col + 3) * 11 +
      (rows + 5) * 7 +
      (cols + 7) * 5 +
      salt) % 3
  Int.ofNat raw - 1

/-- Deterministic row-major matrix fixture of shape `rows x cols`. -/
def flatBasis (rows cols salt : Nat) : Array Int :=
  if rows = 0 || cols = 0 then
    #[]
  else
    (Array.range (rows * cols)).map fun idx =>
      let row := idx / cols
      let col := idx % cols
      entryValue rows cols row col salt

/-- Row-major update-helper fixture with small deterministic entries. -/
def flatUpdateBasis (rows cols salt : Nat) : Array Int :=
  if rows = 0 || cols = 0 then
    #[]
  else
    (Array.range (rows * cols)).map fun idx =>
      let row := idx / cols
      let col := idx % cols
      updateEntryValue rows cols row col salt

/-- Per-parameter fixture: an `n x (2n + 1)` deterministic integer matrix. -/
def prepIntBasisInput (n : Nat) : IntBasisInput :=
  let cols := 2 * n + 1
  { rows := n
    cols := cols
    entries := flatBasis n cols 41 }

/-- Reconstruct a typed dense matrix from row-major entries. -/
def matrixOfFlat (input : IntBasisInput) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

/-- Per-parameter update fixture: a prepared `(n + 3) x (2(n + 3) + 1)`
integer matrix plus fixed legal row-operation indices. -/
def prepUpdateInput (n : Nat) : UpdateInput :=
  let rows := n + 3
  let cols := 2 * rows + 1
  let flat : IntBasisInput :=
    { rows := rows
      cols := cols
      entries := flatUpdateBasis rows cols 83 }
  let sizeReduceSrc : Fin rows := ⟨0, by simp [rows]⟩
  let pivotK : Fin rows := ⟨n + 2, by simp [rows]⟩
  let aboveK : Fin rows := ⟨1, by simp [rows]⟩
  let aboveI : Fin rows := ⟨2, by simp [rows]⟩
  { rows := rows
    cols := cols
    matrix := matrixOfFlat flat
    sizeReduceSrc := sizeReduceSrc
    pivotK := pivotK
    pivotHK := by
      change 0 < n + 2
      omega
    aboveK := aboveK
    aboveHK := by
      change 0 < 1
      omega
    aboveI := aboveI
    coeff := Int.ofNat ((n * 17 + 5) % 9) - 4 }

/-- Stable checksum for natural vectors. -/
def natVectorChecksum (v : Vector Nat n) : Nat :=
  (List.finRange n).foldl
    (fun acc i => acc * 65_537 + v[i])
    0

/-- Stable checksum for integer square matrices. -/
def intMatrixChecksum (M : Matrix Int n n) : Int :=
  (List.finRange n).foldl
    (fun acc i =>
      (List.finRange n).foldl
        (fun rowAcc j => rowAcc * 65_537 + M[i][j])
        acc)
    0

/-- Stable checksum for one integer row. -/
def intRowChecksum (v : Vector Int n) : Int :=
  (List.finRange n).foldl
    (fun acc i => acc * 65_537 + v[i])
    0

/-- Stable checksum for two observed rows of a matrix-valued update. -/
def intRowPairChecksum (M : Matrix Int n m) (i j : Fin n) : Int :=
  intRowChecksum (M.row i) * 65_537 + intRowChecksum (M.row j)

/-- Textbook model for building and eliminating the Gram matrix of `n` rows in
`2n + 1` ambient columns. -/
def gramSurfaceComplexity (n : Nat) : Nat :=
  n * n * n + n * n * (2 * n + 1)

/-- Textbook model for the current full scaled-coefficient determinant surface. -/
def scaledCoeffSurfaceComplexity (n : Nat) : Nat :=
  n * n * gramSurfaceComplexity n

/-- Model for a row update plus checksumming the affected rows in the prepared
`(n + 3) x (2(n + 3) + 1)` fixture. -/
def rowUpdateComplexity (n : Nat) : Nat :=
  2 * (2 * (n + 3) + 1)

/-- Model for one full-size Gram determinant over the prepared update
fixture. -/
def updateGramComplexity (n : Nat) : Nat :=
  gramSurfaceComplexity (n + 3)

/-- Model for update helpers that compute the full scaled-coefficient surface
before extracting their scalar. -/
def updateScaledCoeffComplexity (n : Nat) : Nat :=
  scaledCoeffSurfaceComplexity (n + 3)

/-- Fixed repeat count used to lift very fast row-update helpers above the
child-process measurement floor. This is independent of `n`, so it changes only
the constant factor in the declared linear model. -/
def rowUpdateHotRepeats : Nat := 4096

/-- Repeat a deterministic integer-valued target with a rolling checksum. -/
def repeatIntChecksum (repeats : Nat) (f : Unit → Int) : Int :=
  (List.range repeats).foldl
    (fun acc _ => acc * 65_537 + f ())
    0

/-- Benchmark target: compute all leading Gram determinants and checksum them. -/
def runGramDetVecChecksum (input : IntBasisInput) : Nat :=
  natVectorChecksum (GramSchmidt.Int.gramDetVec (matrixOfFlat input))

/-- Benchmark target: compute the scaled-coefficient matrix and checksum it. -/
def runScaledCoeffsChecksum (input : IntBasisInput) : Int :=
  intMatrixChecksum (GramSchmidt.Int.scaledCoeffs (matrixOfFlat input))

/-- Benchmark target: size-reduce the final row against the first row and
checksum the changed row plus source row. -/
def runSizeReduceChecksum (input : UpdateInput) : Int :=
  repeatIntChecksum rowUpdateHotRepeats fun _ =>
    let reduced :=
      GramSchmidt.Int.sizeReduce input.matrix input.sizeReduceSrc input.pivotK input.coeff
    intRowPairChecksum reduced input.sizeReduceSrc input.pivotK

/-- Benchmark target: swap the final row with its predecessor and checksum the
two affected rows. -/
def runAdjacentSwapChecksum (input : UpdateInput) : Int :=
  repeatIntChecksum rowUpdateHotRepeats fun _ =>
    let swapped := GramSchmidt.Int.adjacentSwap input.matrix input.pivotK input.pivotHK
    intRowPairChecksum swapped (GramSchmidt.prevRow input.pivotK input.pivotHK) input.pivotK

/-- Benchmark target: compute the adjacent-swap denominator. -/
def runAdjacentSwapDenom (input : UpdateInput) : Int :=
  GramSchmidt.Int.adjacentSwapDenom input.matrix input.pivotK

/-- Benchmark target: compute the adjacent-swap pivot coefficient. -/
def runAdjacentSwapPivotCoeff (input : UpdateInput) : Int :=
  GramSchmidt.Int.adjacentSwapPivotCoeff input.matrix input.pivotK input.pivotHK

/-- Benchmark target: compute the adjacent-swap Gram-determinant numerator. -/
def runAdjacentSwapGramDetNumerator (input : UpdateInput) : Int :=
  GramSchmidt.Int.adjacentSwapGramDetNumerator input.matrix input.pivotK input.pivotHK

/-- Benchmark target: compute the adjacent-swap Gram-determinant quotient. -/
def runAdjacentSwapGramDetQuotient (input : UpdateInput) : Int :=
  GramSchmidt.Int.adjacentSwapGramDetQuotient input.matrix input.pivotK input.pivotHK

/-- Benchmark target: compute the above-row previous-column scaled-coefficient
numerator. -/
def runAdjacentSwapScaledCoeffAbovePrevNumerator (input : UpdateInput) : Int :=
  GramSchmidt.Int.adjacentSwapScaledCoeffAbovePrevNumerator
    input.matrix input.aboveK input.aboveHK input.aboveI

/-- Benchmark target: compute the above-row current-column scaled-coefficient
numerator. -/
def runAdjacentSwapScaledCoeffAboveCurrNumerator (input : UpdateInput) : Int :=
  GramSchmidt.Int.adjacentSwapScaledCoeffAboveCurrNumerator
    input.matrix input.aboveK input.aboveHK input.aboveI

setup_benchmark runGramDetVecChecksum n => gramSurfaceComplexity n
  with prep := prepIntBasisInput
  where {
    paramFloor := 8
    paramCeiling := 24
    paramSchedule := .custom #[8, 12, 16, 20, 24]
    maxSecondsPerCall := 3.0
    targetInnerNanos := 200000000
  }

setup_benchmark runScaledCoeffsChecksum n => scaledCoeffSurfaceComplexity n
  with prep := prepIntBasisInput
  where {
    paramFloor := 3
    paramCeiling := 7
    paramSchedule := .custom #[3, 4, 5, 6, 7]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
  }

setup_benchmark runSizeReduceChecksum n => rowUpdateComplexity n
  with prep := prepUpdateInput
  where {
    paramFloor := 64
    paramCeiling := 192
    paramSchedule := .custom #[64, 96, 128, 160, 192]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

setup_benchmark runAdjacentSwapChecksum n => rowUpdateComplexity n
  with prep := prepUpdateInput
  where {
    paramFloor := 64
    paramCeiling := 192
    paramSchedule := .custom #[64, 96, 128, 160, 192]
    maxSecondsPerCall := 2.0
    targetInnerNanos := 200000000
  }

setup_benchmark runAdjacentSwapDenom n => updateGramComplexity n
  with prep := prepUpdateInput
  where {
    paramFloor := 3
    paramCeiling := 6
    paramSchedule := .custom #[3, 4, 5, 6]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runAdjacentSwapPivotCoeff n => updateScaledCoeffComplexity n
  with prep := prepUpdateInput
  where {
    paramFloor := 3
    paramCeiling := 6
    paramSchedule := .custom #[3, 4, 5, 6]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runAdjacentSwapGramDetNumerator n => updateScaledCoeffComplexity n
  with prep := prepUpdateInput
  where {
    paramFloor := 3
    paramCeiling := 6
    paramSchedule := .custom #[3, 4, 5, 6]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runAdjacentSwapGramDetQuotient n => updateScaledCoeffComplexity n
  with prep := prepUpdateInput
  where {
    paramFloor := 3
    paramCeiling := 6
    paramSchedule := .custom #[3, 4, 5, 6]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
    verdictWarmupFraction := 0.25
  }

setup_benchmark runAdjacentSwapScaledCoeffAbovePrevNumerator n =>
    updateScaledCoeffComplexity n
  with prep := prepUpdateInput
  where {
    paramFloor := 3
    paramCeiling := 6
    paramSchedule := .custom #[3, 4, 5, 6]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

setup_benchmark runAdjacentSwapScaledCoeffAboveCurrNumerator n =>
    updateScaledCoeffComplexity n
  with prep := prepUpdateInput
  where {
    paramFloor := 3
    paramCeiling := 6
    paramSchedule := .custom #[3, 4, 5, 6]
    maxSecondsPerCall := 5.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.GramSchmidtBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
