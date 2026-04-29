import HexGramSchmidt
import LeanBench

/-!
Benchmark registrations for `hex-gram-schmidt`.

This Phase 4 slice measures the first executable integer determinant surface:
all leading Gram determinants via `GramSchmidt.Int.gramDetVec`, and the
integral scaled-coefficient matrix via `GramSchmidt.Int.scaledCoeffs`.
Matrix fixture construction is hoisted through `prep`; each timed target
returns a compact checksum instead of the full vector or matrix value.

Scientific registrations:

* `runGramDetVecChecksum`: one Bareiss pass over the Gram matrix, with model
  `O(n^3 + n^2*m)` on deterministic `n x (2n + 1)` integer inputs.
* `runScaledCoeffsChecksum`: the full scaled-coefficient matrix surface, using
  the determinant formula for each lower-triangular entry.

Later slices should add direct benchmark coverage for the row-operation update
helpers in `HexGramSchmidt/Update.lean`; this file intentionally avoids the
noncomputable rational `basis` and `coeffs` APIs.
-/

namespace Hex.GramSchmidtBench

/-- Flattened benchmark input for one integer basis matrix. -/
structure IntBasisInput where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Deterministic small integer entry generator keyed by shape and position. -/
def entryValue (rows cols row col salt : Nat) : Int :=
  let raw :=
    ((row + 1) * 1_103 +
      (col + 3) * 811 +
      (rows + 5) * 97 +
      (cols + 7) * 53 +
      salt) % 31
  Int.ofNat raw - 15

/-- Deterministic row-major matrix fixture of shape `rows x cols`. -/
def flatBasis (rows cols salt : Nat) : Array Int :=
  if rows = 0 || cols = 0 then
    #[]
  else
    (Array.range (rows * cols)).map fun idx =>
      let row := idx / cols
      let col := idx % cols
      entryValue rows cols row col salt

/-- Per-parameter fixture: an `n x (2n + 1)` deterministic integer matrix. -/
def prepIntBasisInput (n : Nat) : IntBasisInput :=
  let cols := 2 * n + 1
  { rows := n
    cols := cols
    entries := flatBasis n cols 41 }

/-- Reconstruct a typed dense matrix from row-major entries. -/
def matrixOfFlat (input : IntBasisInput) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

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

/-- Textbook model for building and eliminating the Gram matrix of `n` rows in
`2n + 1` ambient columns. -/
def gramSurfaceComplexity (n : Nat) : Nat :=
  n * n * n + n * n * (2 * n + 1)

/-- Textbook model for the current full scaled-coefficient determinant surface. -/
def scaledCoeffSurfaceComplexity (n : Nat) : Nat :=
  n * n * gramSurfaceComplexity n

/-- Benchmark target: compute all leading Gram determinants and checksum them. -/
def runGramDetVecChecksum (input : IntBasisInput) : Nat :=
  natVectorChecksum (GramSchmidt.Int.gramDetVec (matrixOfFlat input))

/-- Benchmark target: compute the scaled-coefficient matrix and checksum it. -/
def runScaledCoeffsChecksum (input : IntBasisInput) : Int :=
  intMatrixChecksum (GramSchmidt.Int.scaledCoeffs (matrixOfFlat input))

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

end Hex.GramSchmidtBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
