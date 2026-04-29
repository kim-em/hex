import HexMatrix
import LeanBench

/-!
Benchmark registrations for `hex-matrix`.

This Phase 4 slice measures dense square matrix multiplication and determinant
computation on deterministically generated integer inputs. Matrix construction
is hoisted into `prep` for every parametric family, so each declared model
tracks the timed algebraic operation rather than fixture construction.

Scientific registrations:

* `runSquareMulChecksum`: dense square multiplication, `O(n^3)`.
* `runBareissDet`: row-pivoted Bareiss determinant over `Int`, `O(n^3)`.

Small-domain cross-check registrations:

* `runLeibnizDet`: generic Leibniz determinant, `O(n * n!)`, capped at small
  dimensions so `compare runBareissDet runLeibnizDet` exercises the shared
  determinant API where both implementations are practical.
-/

namespace Hex.MatrixBench

/-- Flattened benchmark input for square matrix multiplication. The arrays
store `n * n` entries in row-major order. -/
structure MulInput where
  n : Nat
  lhs : Array Int
  rhs : Array Int
  deriving Repr, BEq, Hashable

/-- Flattened benchmark input for one square integer matrix. -/
structure DetInput where
  n : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Deterministic pseudo-random-looking entry generator keyed by matrix
dimension, coordinates, and a salt distinguishing the two operands. -/
def entryValue (n row col salt : Nat) : Int :=
  let x : UInt64 :=
    (((n.toUInt64 + 1) * 0x9E3779B97F4A7C15) +
      ((row.toUInt64 + 1) * 0xBF58476D1CE4E5B9) +
      ((col.toUInt64 + 1) * 0x94D049BB133111EB) +
      salt.toUInt64)
  Int.ofNat (x.toNat % 65_521)

/-- Small signed deterministic entries for determinant benchmarks. Keeping
coefficients small makes the Bareiss registration test elimination scaling
rather than artificial coefficient growth in the fixture generator. -/
def smallEntryValue (n row col salt : Nat) : Int :=
  let x := entryValue n row col salt
  (x % 11) - 5

/-- Deterministic row-major matrix fixture of shape `n × n`. -/
def flatMatrix (n salt : Nat) : Array Int :=
  if n = 0 then
    #[]
  else
    (Array.range (n * n)).map fun idx =>
      let row := idx / n
      let col := idx % n
      entryValue n row col salt

/-- Deterministic small-entry row-major matrix fixture of shape `n × n`. -/
def flatSmallMatrix (n salt : Nat) : Array Int :=
  if n = 0 then
    #[]
  else
    (Array.range (n * n)).map fun idx =>
      let row := idx / n
      let col := idx % n
      smallEntryValue n row col salt

/-- Per-parameter benchmark fixture: two deterministic square matrices. -/
def prepMulInput (n : Nat) : MulInput :=
  { n := n
    lhs := flatMatrix n 17
    rhs := flatMatrix n 43 }

/-- Per-parameter determinant fixture: one deterministic square matrix. -/
def prepDetInput (n : Nat) : DetInput :=
  { n := n
    entries := flatSmallMatrix n 71 }

/-- Reconstruct a typed dense square matrix from a row-major array. -/
def matrixOfFlat (n : Nat) (entries : Array Int) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j => entries.getD (i.val * n + j.val) 0

/-- Sum every entry so the benchmark returns a hashable observable of the
matrix product rather than the full matrix value. -/
def checksum (M : Hex.Matrix Int n n) : Int :=
  (List.finRange n).foldl
    (fun acc i =>
      (List.finRange n).foldl (fun rowAcc j => rowAcc + M[i][j]) acc)
    0

/-- Benchmark target: multiply the prepared matrices and checksum the
result. The timed work remains cubic in the matrix dimension. -/
def runSquareMulChecksum (input : MulInput) : Int :=
  let lhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.lhs
  let rhs : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.rhs
  checksum (lhs * rhs)

/-- Benchmark target: compute the determinant using row-pivoted Bareiss
elimination. Fixture construction is supplied by `prepDetInput`. -/
def runBareissDet (input : DetInput) : Int :=
  let M : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.entries
  Hex.Matrix.bareiss M

/-- Benchmark target: compute the same determinant using the generic Leibniz
definition. This is intended only for small-domain conformance comparison. -/
def runLeibnizDet (input : DetInput) : Int :=
  let M : Hex.Matrix Int input.n input.n := matrixOfFlat input.n input.entries
  Hex.Matrix.det M

/-- Textbook operation-count model for the generic Leibniz determinant path. -/
def leibnizDetComplexity : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * leibnizDetComplexity n

setup_benchmark runSquareMulChecksum n => n * n * n
  with prep := prepMulInput
  where {
    paramFloor := 4
    paramCeiling := 64
    maxSecondsPerCall := 0.5
    targetInnerNanos := 200000000
  }

setup_benchmark runBareissDet n => n * n * n
  with prep := prepDetInput
  where {
    paramFloor := 4
    paramCeiling := 64
    maxSecondsPerCall := 1.5
    targetInnerNanos := 800000000
  }

setup_benchmark runLeibnizDet n => n * leibnizDetComplexity n
  with prep := prepDetInput
  where {
    paramFloor := 2
    paramCeiling := 7
    maxSecondsPerCall := 1.5
    targetInnerNanos := 800000000
  }

end Hex.MatrixBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
