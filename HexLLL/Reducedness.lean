import HexLLL.Core

/-!
Reducedness-predicate scaffolding for LLL bases.

This module adds the spec-facing predicate layer for `HexLLL`: the
size-reduced condition, the Lovasz condition, and the combined
`isLLLReduced` predicate on integer bases parameterized by `δ`.
-/

namespace HexLLL

open HexMatrix

/--
The size-reduced half of the `δ`-LLL predicate.

Every strict lower-triangular Gram-Schmidt coefficient has absolute
value at most `1 / 2`.
-/
def isSizeReduced (b : HexMatrix.Matrix Int n m) : Prop :=
  ∀ i j : Nat, j < i → i < n →
    -(1 / 2 : Rat) ≤ HexMatrix.Matrix.entry (Hex.GramSchmidt.Int.coeffs b) i j ∧
      HexMatrix.Matrix.entry (Hex.GramSchmidt.Int.coeffs b) i j ≤ (1 / 2 : Rat)

/--
The Lovasz half of the `δ`-LLL predicate.

For each adjacent pair of Gram-Schmidt basis vectors, the usual
`δ`-parameterized Lovasz inequality holds.
-/
def satisfiesLovasz (b : HexMatrix.Matrix Int n m) (δ : Rat) : Prop :=
  ∀ i : Nat, i + 1 < n →
    (δ - HexMatrix.Matrix.entry (Hex.GramSchmidt.Int.coeffs b) (i + 1) i ^ (2 : Nat)) *
        HexMatrix.Vector.normSq (HexMatrix.Matrix.row (Hex.GramSchmidt.Int.basis b) i) ≤
      HexMatrix.Vector.normSq (HexMatrix.Matrix.row (Hex.GramSchmidt.Int.basis b) (i + 1))

/-- A basis is `δ`-LLL-reduced when it is size-reduced and satisfies Lovasz. -/
def isLLLReduced (b : HexMatrix.Matrix Int n m) (δ : Rat) : Prop :=
  isSizeReduced b ∧ satisfiesLovasz b δ

end HexLLL
