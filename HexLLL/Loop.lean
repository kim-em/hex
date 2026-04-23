import HexLLL.SwapStep

/-!
Executable outer-loop scaffolding for the LLL integer state.

This module adds the public loop entrypoints promised by the `HexLLL`
specification. Phase 1 keeps the implementation intentionally narrow: a
single executable Lovasz-condition check, the next-index helper for the
swap branch, a one-step transition on `LLLState`, and a fuelled outer
loop used to expose the spec-facing `lllAux` and `lll` names without
committing yet to the proof-heavy termination argument.
-/

namespace HexLLL

open HexMatrix

namespace LLLState

/-- Integer-valued left side of the Lovasz inequality at index `k`. -/
def lovaszLeft (s : LLLState n m) (k : Nat) : Rat :=
  (s.gramDetEntry (k + 1) : Rat) * (s.gramDetEntry (k - 1) : Rat) +
    (swapPivotCoeff s k : Rat) ^ (2 : Nat)

/-- Integer-valued right side of the Lovasz inequality at index `k`. -/
def lovaszRight (s : LLLState n m) (k : Nat) (δ : Rat) : Rat :=
  δ * (s.gramDetEntry k : Rat) ^ (2 : Nat)

/-- Boolean Lovasz-condition check for the current pivot index. -/
def lovaszHolds (s : LLLState n m) (k : Nat) (δ : Rat) : Bool :=
  decide (lovaszRight s k δ ≤ lovaszLeft s k)

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

/--
Fuelled executable outer loop used by the public `lllAux` entrypoint.

Running out of fuel returns the current basis unchanged; later proof
work can replace this with the spec's well-founded recursion.
-/
def loopWithFuel : Nat → LLLState n m → Nat → Rat → HexMatrix.Matrix Int n m
  | 0, s, _, _ => s.b
  | fuel + 1, s, k, δ =>
      if _hkn : k = n then
        s.b
      else
        let (sNext, kNext) := loopStep s k δ
        loopWithFuel fuel sNext kNext δ

end LLLState

/--
Executable outer LLL loop entrypoint.

Phase 1 exposes the final API shape while using a simple fuel bound
derived from the current potential and remaining index distance.
-/
def lllAux (s : LLLState n m) (k : Nat) (δ : Rat)
    (_hδ : 1 / 4 < δ) (_hδ' : δ ≤ 1) (_hind : s.b.independent)
    (_hk : 1 ≤ k) (_hkn : k ≤ n) : HexMatrix.Matrix Int n m :=
  s.loopWithFuel (s.potential + (n - k) + 1) k δ

/--
Top-level LLL entrypoint starting from the canonical integer state
derived from the input basis.
-/
def lll (b : HexMatrix.Matrix Int n m) (δ : Rat)
    (hδ : 1 / 4 < δ) (hδ' : δ ≤ 1) (_hn : 1 ≤ n) (hind : b.independent) :
    HexMatrix.Matrix Int n m :=
  lllAux (LLLState.ofBasis b) 1 δ hδ hδ' hind (by omega) (by omega)

end HexLLL
