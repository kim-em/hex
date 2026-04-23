import HexPolyFp.Frobenius
import HexPolyFp.ModCompose

/-!
# `HexPolyFp` -- core conformance

Deterministic Lean-only conformance checks for the modular-power,
Frobenius, and modular-composition surface of `HexPolyFp`. Every check
elaborates as part of `lake build HexPolyFp`, so regressions in these
executable quotient-ring operations fail CI immediately.

**Conformance contract for this slice:**

- **Oracle:** `none`. The `core` profile for this slice uses committed
  small-prime examples together with internal agreement theorems and
  reduced-remainder invariants.
- **Mode:** `always`.
- **Covered operations:** `HexPolyFp.FpPoly.powModMonic`,
  `HexPolyFp.FpPoly.frobeniusModMonic`,
  `HexPolyFp.FpPoly.frobeniusPowModMonic`,
  `HexPolyFp.FpPoly.modComposeMonic`.
- **Covered properties:**
  - modular powers stay normalized and idempotent under
    `modMonic`, agree with the naive repeated-multiplication
    specification, and stay below the monic modulus degree on
    committed nonzero moduli;
  - Frobenius agrees with `powModMonic` at exponent `p`, stays
    normalized, and stays below the monic modulus degree on committed
    examples;
  - iterated Frobenius agrees with the repeated single-step iterator,
    respects the `k = 0` base case, stays normalized, and stays below
    the monic modulus degree on committed examples;
  - modular composition agrees with dense composition followed by
    `modMonic`, stays normalized, is idempotent under `modMonic`, and
    stays below the monic modulus degree on committed nonzero moduli.
- **Covered edge cases:** exponent `0` for modular power, zero
  polynomial inputs for Frobenius and modular composition, linear
  monic moduli, and trailing-zero coefficient arrays that must
  normalize before modular reduction.
-/

namespace HexPolyFp
namespace Conformance
open HexModArith
open HexPolyFp.FpPoly

private abbrev P3 := HexPolyFp.FpPoly 3
private abbrev P5 := HexPolyFp.FpPoly 5

private def coeffsToNat {p : Nat} [NeZero p] (f : HexPolyFp.FpPoly p) : List Nat :=
  f.coeffs.toList.map fun a => a.toNat

private def poly3 (xs : List Nat) : P3 :=
  HexPolyFp.FpPoly.ofCoeffs ((xs.map fun n : Nat => (n : ZMod64 3)).toArray)

private def poly5 (xs : List Nat) : P5 :=
  HexPolyFp.FpPoly.ofCoeffs ((xs.map fun n : Nat => (n : ZMod64 5)).toArray)

private def powTypicalBase : P5 := poly5 [3, 4, 1]
private def powTypicalModulus : P5 := poly5 [2, 0, 1]
private def powTypicalResult : P5 := powModMonic powTypicalBase 5 powTypicalModulus

private def powEdgeBase : P3 := poly3 [2, 1]
private def powEdgeModulus : P3 := poly3 [1, 1, 1]
private def powEdgeResult : P3 := powModMonic powEdgeBase 0 powEdgeModulus

private def powAdversarialBase : P3 := poly3 [0, 2, 0, 0]
private def powAdversarialModulus : P3 := poly3 [1, 1]
private def powAdversarialResult : P3 := powModMonic powAdversarialBase 4 powAdversarialModulus

private def frobeniusEdgeModulus : P3 := poly3 [1, 1]
private def frobeniusAdversarialBase : P3 := poly3 [1, 2, 1]
private def frobeniusAdversarialModulus : P3 := poly3 [2, 1, 0, 1]

private def frobeniusPowTypicalResult : P5 :=
  frobeniusPowModMonic powTypicalBase powTypicalModulus 2

private def frobeniusPowAdversarialBase : P3 := poly3 [2, 0, 0, 1]
private def frobeniusPowAdversarialModulus : P3 := poly3 [1, 2, 0, 1]
private def frobeniusPowAdversarialResult : P3 :=
  frobeniusPowModMonic frobeniusPowAdversarialBase frobeniusPowAdversarialModulus 3

private def composeTypicalOuter : P5 := poly5 [4, 0, 1]
private def composeTypicalInner : P5 := poly5 [1, 1]
private def composeTypicalModulus : P5 := poly5 [2, 0, 1]
private def composeTypicalResult : P5 :=
  modComposeMonic composeTypicalOuter composeTypicalInner composeTypicalModulus

private def composeEdgeInner : P3 := poly3 [1, 2]
private def composeEdgeModulus : P3 := poly3 [1, 1]
private def composeAdversarialOuter : P3 := poly3 [1, 0, 2, 0, 0]
private def composeAdversarialInner : P3 := poly3 [2, 1]
private def composeAdversarialModulus : P3 := poly3 [2, 1, 1]
private def composeAdversarialResult : P3 :=
  modComposeMonic composeAdversarialOuter composeAdversarialInner composeAdversarialModulus

/-! ## `FpPoly.powModMonic` -/

/-- info: [1, 1] -/
#guard_msgs in
#eval! coeffsToNat powTypicalResult

/-- info: [1] -/
#guard_msgs in
#eval! coeffsToNat powEdgeResult

/-- info: [1] -/
#guard_msgs in
#eval! coeffsToNat powAdversarialResult

example : HexPoly.DensePoly.IsNormalized powTypicalResult.coeffs :=
  powModMonic_isNormalized _ _ _

example : HexPoly.DensePoly.IsNormalized powEdgeResult.coeffs :=
  powModMonic_isNormalized _ _ _

example : HexPoly.DensePoly.IsNormalized powAdversarialResult.coeffs :=
  powModMonic_isNormalized _ _ _

#guard decide (coeffsToNat (modMonic powTypicalResult powTypicalModulus) = coeffsToNat powTypicalResult)
#guard decide (coeffsToNat powEdgeResult = coeffsToNat (naivePowModMonic powEdgeBase powEdgeModulus 0))
#guard decide
  (coeffsToNat powAdversarialResult =
    coeffsToNat (naivePowModMonic powAdversarialBase powAdversarialModulus 4))
#guard decide (powTypicalResult.natDegree? = none ∨ powTypicalResult.degree < powTypicalModulus.degree)
#guard decide
  (powAdversarialResult.natDegree? = none ∨
    powAdversarialResult.degree < powAdversarialModulus.degree)

/-! ## `FpPoly.frobeniusModMonic` -/

/-- info: [1, 1] -/
#guard_msgs in
#eval! coeffsToNat (frobeniusModMonic powTypicalBase powTypicalModulus)

/-- info: [] -/
#guard_msgs in
#eval! coeffsToNat (frobeniusModMonic (0 : P3) frobeniusEdgeModulus)

/-- info: [1, 2, 1] -/
#guard_msgs in
#eval! coeffsToNat (frobeniusModMonic frobeniusAdversarialBase frobeniusAdversarialModulus)

example : HexPoly.DensePoly.IsNormalized (frobeniusModMonic powTypicalBase powTypicalModulus).coeffs :=
  frobeniusModMonic_isNormalized _ _

example : HexPoly.DensePoly.IsNormalized (frobeniusModMonic (0 : P3) frobeniusEdgeModulus).coeffs :=
  frobeniusModMonic_isNormalized _ _

example :
    HexPoly.DensePoly.IsNormalized
      (frobeniusModMonic frobeniusAdversarialBase frobeniusAdversarialModulus).coeffs :=
  frobeniusModMonic_isNormalized _ _

#guard decide
  (coeffsToNat (frobeniusModMonic powTypicalBase powTypicalModulus) =
    coeffsToNat (powModMonic powTypicalBase 5 powTypicalModulus))
#guard decide
  (coeffsToNat (modMonic (frobeniusModMonic powTypicalBase powTypicalModulus) powTypicalModulus) =
    coeffsToNat (frobeniusModMonic powTypicalBase powTypicalModulus))
#guard decide
  ((frobeniusModMonic frobeniusAdversarialBase frobeniusAdversarialModulus).natDegree? = none ∨
    (frobeniusModMonic frobeniusAdversarialBase frobeniusAdversarialModulus).degree <
      frobeniusAdversarialModulus.degree)

/-! ## `FpPoly.frobeniusPowModMonic` -/

/-- info: [1, 4] -/
#guard_msgs in
#eval! coeffsToNat frobeniusPowTypicalResult

/-- info: [] -/
#guard_msgs in
#eval! coeffsToNat (frobeniusPowModMonic (0 : P3) frobeniusEdgeModulus 0)

/-- info: [1, 1] -/
#guard_msgs in
#eval! coeffsToNat frobeniusPowAdversarialResult

example : HexPoly.DensePoly.IsNormalized frobeniusPowTypicalResult.coeffs :=
  frobeniusPowModMonic_isNormalized _ _ _

example : HexPoly.DensePoly.IsNormalized (frobeniusPowModMonic (0 : P3) frobeniusEdgeModulus 0).coeffs :=
  frobeniusPowModMonic_isNormalized _ _ _

example : HexPoly.DensePoly.IsNormalized frobeniusPowAdversarialResult.coeffs :=
  frobeniusPowModMonic_isNormalized _ _ _

#guard decide
  (coeffsToNat (frobeniusPowModMonic (0 : P3) frobeniusEdgeModulus 0) =
    coeffsToNat (modMonic (0 : P3) frobeniusEdgeModulus))
#guard decide
  (coeffsToNat frobeniusPowTypicalResult =
    coeffsToNat (iterateFrobeniusModMonic powTypicalModulus 2 powTypicalBase))
#guard decide
  (coeffsToNat (modMonic frobeniusPowAdversarialResult frobeniusPowAdversarialModulus) =
    coeffsToNat frobeniusPowAdversarialResult)
#guard decide
  (frobeniusPowAdversarialResult.natDegree? = none ∨
    frobeniusPowAdversarialResult.degree < frobeniusPowAdversarialModulus.degree)

/-! ## `FpPoly.modComposeMonic` -/

/-- info: [3, 2] -/
#guard_msgs in
#eval! coeffsToNat composeTypicalResult

/-- info: [] -/
#guard_msgs in
#eval! coeffsToNat (modComposeMonic (0 : P3) composeEdgeInner composeEdgeModulus)

/-- info: [2] -/
#guard_msgs in
#eval! coeffsToNat composeAdversarialResult

example : HexPoly.DensePoly.IsNormalized composeTypicalResult.coeffs :=
  modComposeMonic_isNormalized _ _ _

example :
    HexPoly.DensePoly.IsNormalized (modComposeMonic (0 : P3) composeEdgeInner composeEdgeModulus).coeffs :=
  modComposeMonic_isNormalized _ _ _

example : HexPoly.DensePoly.IsNormalized composeAdversarialResult.coeffs :=
  modComposeMonic_isNormalized _ _ _

#guard decide
  (coeffsToNat composeTypicalResult =
    coeffsToNat
      (modMonic
        (HexPoly.DensePoly.compose (R := ZMod64 5) composeTypicalOuter composeTypicalInner)
        composeTypicalModulus))
#guard decide
  (coeffsToNat (modMonic composeTypicalResult composeTypicalModulus) = coeffsToNat composeTypicalResult)
#guard decide
  (coeffsToNat (modComposeMonic (0 : P3) composeEdgeInner composeEdgeModulus) =
    coeffsToNat (0 : P3))
#guard decide
  (composeAdversarialResult.natDegree? = none ∨
    composeAdversarialResult.degree < composeAdversarialModulus.degree)

end Conformance
end HexPolyFp
