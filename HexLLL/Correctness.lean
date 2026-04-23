import HexLLL.Loop
import HexLLL.Reducedness

/-!
Correctness-theorem scaffolding for the public LLL API.

This module adds the remaining Phase 1 declarations promised by the
`HexLLL` specification: lattice preservation, reducedness of the output
basis, and the standard short-vector bound. The proofs remain deferred
to later phases, but the theorem surface is now available to downstream
libraries.
-/

namespace HexLLL

open HexMatrix

/--
Approximation factor appearing in the standard LLL short-vector bound.

Phase 1 exposes this helper so the public theorem statement stays close
to the specification without repeating the rational expression inline.
-/
noncomputable def shortVectorFactor (δ : Rat) : Rat :=
  1 / (δ - 1 / 4)

/--
The LLL-reduced basis spans the same integer lattice as the input.
-/
theorem lll_same_lattice (b : HexMatrix.Matrix Int n m) (δ : Rat)
    (hδ : 1 / 4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hli : b.independent)
    (v : Vector Int m) :
    (lll b δ hδ hδ' hn hli).memLattice v ↔ b.memLattice v := by
  sorry

/--
The public `lll` output satisfies the scaffolded `δ`-LLL reducedness
predicate.
-/
theorem lll_reduced (b : HexMatrix.Matrix Int n m) (δ : Rat)
    (hδ : 1 / 4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hli : b.independent) :
    isLLLReduced (lll b δ hδ hδ' hn hli) δ := by
  sorry

/--
Standard short-vector guarantee for the first LLL output row.
-/
theorem lll_short_vector (b : HexMatrix.Matrix Int n m) (δ : Rat)
    (hδ : 1 / 4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hli : b.independent)
    (v : Vector Int m) :
    b.memLattice v → v ≠ 0 →
      ((HexMatrix.Vector.normSq
          (HexMatrix.Matrix.row (R := Int) (n := n) (m := m) (lll b δ hδ hδ' hn hli) 0) : Int) : Rat) ≤
        shortVectorFactor δ ^ (n - 1) * HexMatrix.Vector.normSq v := by
  sorry

end HexLLL
