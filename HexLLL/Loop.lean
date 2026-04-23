import HexLLL.SwapStep

/-!
Executable outer-loop definitions for the LLL integer state.

This module exposes the public `lllAux` and `lll` entrypoints from the
`HexLLL` specification. The executable path follows the spec's exact
control flow: size-reduce first, then branch on the integer
cross-multiplied Lovasz inequality, advancing on success and swapping on
failure.
-/

namespace HexLLL

open HexMatrix

namespace LLLState

/-- Integer-valued left side of the Lovasz inequality at index `k`. -/
def lovaszLeft (s : LLLState n m) (k : Nat) : Nat :=
  s.gramDetEntry (k + 1) * s.gramDetEntry (k - 1) + Int.natAbs (swapPivotCoeff s k) ^ 2

/-- Integer-valued right side of the cross-multiplied Lovasz inequality. -/
def lovaszRight (s : LLLState n m) (k : Nat) (δ : Rat) : Nat :=
  Int.natAbs δ.num * s.gramDetEntry k ^ 2

/-- Boolean Lovasz-condition check for the current pivot index. -/
def lovaszHolds (s : LLLState n m) (k : Nat) (δ : Rat) : Bool :=
  decide (lovaszRight s k δ ≤ δ.den * lovaszLeft s k)

/--
Index used after a swap branch in the outer loop.

The LLL loop never drops below `1`, even when swapping at `k = 1`.
-/
def nextIndexAfterSwap (k : Nat) : Nat :=
  max (k - 1) 1

/--
Perform one outer-loop transition at index `k`.

The step always size-reduces first, then either advances or swaps
depending on the Lovasz-condition branch.
-/
def loopStep (s : LLLState n m) (k : Nat) (δ : Rat) : LLLState n m × Nat :=
  let sReduced := s.sizeReduce k
  if lovaszHolds sReduced k δ then
    (sReduced, k + 1)
  else
    let sSwapped := sReduced.swapStep k
    (sSwapped, nextIndexAfterSwap k)

end LLLState

/--
Executable outer LLL loop entrypoint.

The recursion matches the specification's integer-state loop: stop at
`k = n`, otherwise size-reduce first and then either advance or swap.
-/
def lllAux (s : LLLState n m) (k : Nat) (δ : Rat)
    (_hδ : 1 / 4 < δ) (_hδ' : δ ≤ 1) (_hind : s.b.independent)
    (_hk : 1 ≤ k) (_hkn : k ≤ n) : HexMatrix.Matrix Int n m :=
  if h : k = n then
    s.b
  else
    let sReduced := s.sizeReduce k
    if sReduced.lovaszHolds k δ then
      lllAux sReduced (k + 1) δ _hδ _hδ' (by sorry) (by omega) (by omega)
    else
      let sSwapped := sReduced.swapStep k
      lllAux sSwapped (LLLState.nextIndexAfterSwap k) δ _hδ _hδ' (by sorry) (by sorry) (by sorry)
termination_by (s.potential, n - k)
decreasing_by
  all_goals
    sorry

/--
Top-level LLL entrypoint starting from the canonical integer state
derived from the input basis.
-/
def lll (b : HexMatrix.Matrix Int n m) (δ : Rat)
    (hδ : 1 / 4 < δ) (hδ' : δ ≤ 1) (_hn : 1 ≤ n) (hind : b.independent) :
    HexMatrix.Matrix Int n m :=
  lllAux (LLLState.ofBasis b) 1 δ hδ hδ' hind (by omega) (by omega)

end HexLLL
