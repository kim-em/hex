import HexLLL.Core

/-!
Integer state scaffolding for the LLL reduction loop.

This module adds the executable `HexLLL` state surface promised by the
specification: an integer-only `LLLState` record tracking the current
basis, scaled Gram-Schmidt coefficients, and leading Gram determinants,
together with the Nat-indexed Gram-determinant accessor, the single
coefficient recovery helper used by the proof layer, and the
multiplicative potential that later termination arguments decrease.
-/

namespace HexLLL

open HexMatrix

/--
Executable integer state for the scaffolded LLL loop.

The stored data are entirely integral; the proof fields relate them to
the rational Gram-Schmidt quantities exposed by `HexGramSchmidt`.
-/
structure LLLState (n m : Nat) where
  b : HexMatrix.Matrix Int n m
  ν : HexMatrix.Matrix Int n n
  d : Vector Nat (n + 1)
  ν_eq : ∀ (i j : Fin n), j.1 < i.1 →
    (((ν[i][j] : Int) : Rat) =
      (d.get ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ : Rat) *
        HexMatrix.Matrix.entry (Hex.GramSchmidt.Int.coeffs b) i.1 j.1)
  d_eq : ∀ i : Fin (n + 1),
    d.get i = Hex.GramSchmidt.Int.gramDet b i.1 (Nat.le_of_lt_succ i.2)

namespace LLLState

/--
Nat-indexed access to the stored leading Gram determinants.

Out-of-bounds indices return `0`, matching the Nat-indexed matrix lookup
helpers used elsewhere in the scaffold.
-/
def gramDetEntry (s : LLLState n m) (k : Nat) : Nat :=
  if hk : k < n + 1 then
    s.d.get ⟨k, hk⟩
  else
    0

/--
Recover a single rational Gram-Schmidt coefficient from the integer
state.

This projection is used by the proof layer; the executable state keeps
only the scaled integer coefficients and Gram determinants.
-/
noncomputable def gramSchmidtCoeff (s : LLLState n m) (i j : Nat) : Rat :=
  ((HexMatrix.Matrix.entry s.ν i j : Int) : Rat) / (gramDetEntry s (j + 1) : Rat)

/--
Multiplicative potential used by the later LLL termination argument.

Phase 1 keeps this executable as the product of the stored nontrivial
leading Gram determinants `d₁ * ... * dₙ₋₁`.
-/
def potential (s : LLLState n m) : Nat :=
  ((List.range n).drop 1).foldl
    (fun acc k => acc * s.gramDetEntry k)
    1

end LLLState
end HexLLL
