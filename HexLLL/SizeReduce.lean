import HexLLL.State

/-!
Executable size-reduction scaffolding for the LLL integer state.

This module extends the `HexLLL` Phase 1 scaffold with the first
algorithmic state transition from the specification: size reduction of a
fixed row `k` against earlier rows. The executable content is the
Nat-indexed reduction loop and the associated rounding helper; the proof
fields reconnecting the updated integer state to Gram-Schmidt data stay
in the theorem layer.
-/

namespace HexLLL

open HexMatrix

namespace LLLState

/--
Rebuild an `LLLState` from a basis matrix by recomputing the stored
scaled Gram-Schmidt coefficients and leading Gram determinants.
-/
def ofBasis (b : HexMatrix.Matrix Int n m) : LLLState n m :=
  { b := b
    ν := Hex.GramSchmidt.Int.scaledCoeffs b
    d := Hex.GramSchmidt.Int.gramDetVec b
    ν_eq := by
      intro i j hij
      sorry
    d_eq := by
      intro i
      sorry }

/--
The nearest-integer quotient used by the size-reduction update rule.

This implements the spec's floor-division formula
`⌊(2 * ν[k,j] + d[j+1]) / (2 * d[j+1])⌋`.
-/
def sizeReduceFactor (s : LLLState n m) (k j : Nat) : Int :=
  let νkj := HexMatrix.Matrix.entry s.ν k j
  let dj := (s.gramDetEntry (j + 1) : Int)
  Int.fdiv (2 * νkj + dj) (2 * dj)

/--
Apply the single-column size-reduction update at `(k, j)` when the
stored scaled coefficient violates the `|coeff| ≤ 1/2` bound.
-/
def sizeReduceStep (s : LLLState n m) (k j : Nat) : LLLState n m :=
  if _hk : k < n then
    if _hjk : j < k then
      if _hreduce : 2 * Int.natAbs (HexMatrix.Matrix.entry s.ν k j) > s.gramDetEntry (j + 1) then
        ofBasis (Hex.GramSchmidt.Int.sizeReduce s.b k j (sizeReduceFactor s k j))
      else
        s
    else
      s
  else
    s

/--
Size-reduce row `k` against rows `j, j - 1, ..., 0`.

The recursion follows the descending-column order from the LLL
specification.
-/
def sizeReduceFrom (s : LLLState n m) (k : Nat) : Nat -> LLLState n m
  | 0 => sizeReduceStep s k 0
  | j + 1 => sizeReduceFrom (sizeReduceStep s k (j + 1)) k j

/--
Size-reduce row `k` against all earlier rows.

Out-of-bounds `k` and the vacuous `k = 0` case leave the state
unchanged.
-/
def sizeReduce (s : LLLState n m) (k : Nat) : LLLState n m :=
  if _hk : k < n then
    if _hk0 : k = 0 then
      s
    else
      sizeReduceFrom s k (k - 1)
  else
    s

end LLLState
end HexLLL
