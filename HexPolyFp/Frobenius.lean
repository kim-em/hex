import HexPolyFp.Basic

/-!
Frobenius-style power maps in `F_p[x]`.

The executable API here computes `X^p mod f` and `X^(p^k) mod f` by
repeated squaring with reduction modulo a monic polynomial, matching the
specialized polynomial layer expected by Berlekamp- and Hensel-style
consumers. Modular composition lives separately in `HexPolyFp.ModCompose`.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/--
Exponentiation by squaring in the quotient `F_p[x] / (f)`, reducing after
every multiplication with the executable `DensePoly.modByMonic` routine.
-/
private def powModMonicAux
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Nat → FpPoly p → FpPoly p → FpPoly p
  | 0, _, acc => acc
  | n + 1, base, acc =>
      let acc' :=
        if (n + 1) % 2 = 0 then
          acc
        else
          modByMonic f (acc * base) hmonic
      let base' := modByMonic f (base * base) hmonic
      powModMonicAux f hmonic ((n + 1) / 2) base' acc'
termination_by n => n
decreasing_by
  simpa using Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 2)

/-- Compute `base^n mod f` for monic `f`. -/
def powModMonic (base f : FpPoly p) (hmonic : DensePoly.Monic f) (n : Nat) :
    FpPoly p :=
  powModMonicAux f hmonic n (modByMonic f base hmonic) 1

/-- Compute `X^p mod f`, the basic Frobenius generator used downstream. -/
def frobeniusXMod (f : FpPoly p) (hmonic : DensePoly.Monic f) : FpPoly p :=
  powModMonic X f hmonic p

/-- Compute `X^(p^k) mod f` for arbitrary `k`. -/
def frobeniusXPowMod (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    FpPoly p :=
  powModMonic X f hmonic (p ^ k)

@[simp] theorem frobeniusXPowMod_zero
    [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    frobeniusXPowMod f hmonic 0 = modByMonic f X hmonic := by
  simp [frobeniusXPowMod, powModMonic, powModMonicAux, modByMonic,
    DensePoly.modByMonic_eq_mod, DensePoly.mod_mod]

end FpPoly
end Hex
