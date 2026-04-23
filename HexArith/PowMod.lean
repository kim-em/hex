/-!
Nat-level modular exponentiation scaffolding.

This module provides the Phase 1 executable `powMod` API and its key
correctness statement for the arithmetic library.
-/

namespace HexArith

/--
Fuel-bounded exponentiation by squaring.

The accumulator and base are reduced modulo `p` at each step so the
definition is executable while staying close to the later Montgomery
implementation boundary.
-/
private def powModAux (p : Nat) (base acc : Nat) : Nat → Nat
  | 0 => acc % p
  | n + 1 =>
      let exp := n + 1
      let acc' := if exp % 2 = 0 then acc % p else (acc * base) % p
      let base' := (base * base) % p
      powModAux p base' acc' (exp / 2)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- Modular exponentiation by squaring. -/
def powMod (a n p : Nat) : Nat :=
  powModAux p (a % p) (1 % p) n

theorem powMod_eq (a n p : Nat) (hp : p > 0) :
    powMod a n p = a ^ n % p := by
  sorry

end HexArith
