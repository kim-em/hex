/-!
Nat- and `UInt64`-level Montgomery inverse scaffolding.

This module provides the Phase 1 executable inverse API used to produce
the Montgomery constant `p'` satisfying `p * p' ≡ -1 mod 2^64`.
-/

namespace HexArith

private def montgomeryInvRadix : Nat :=
  2 ^ 64

/-- Search `[0, bound)` for a witness satisfying `pred`, defaulting to `0`. -/
private def findWitness (bound : Nat) (pred : Nat → Bool) : Nat :=
  match (List.range bound).find? pred with
  | some n => n
  | none => 0

/--
Compute a concrete positive inverse of `p` modulo `2^64`.

Phase 1 uses bounded search to provide a real executable body; later phases
can refine this to the intended Newton iteration without changing the API.
-/
def montPosInv (p : UInt64) : UInt64 :=
  .ofNat <| findWitness montgomeryInvRadix fun x => (p.toNat * x) % montgomeryInvRadix == 1

theorem montPosInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montPosInv p).toNat % (2 ^ 64) = 1 := by
  sorry

/-- Negate the positive inverse to obtain the standard Montgomery `p'`. -/
def montInv (p : UInt64) : UInt64 :=
  0 - montPosInv p

theorem montInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montInv p).toNat % (2 ^ 64) = 2 ^ 64 - 1 := by
  sorry

end HexArith
