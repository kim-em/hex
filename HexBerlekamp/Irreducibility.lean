import HexBerlekamp.Basic

/-!
Executable irreducibility tests for `hex-berlekamp`.

This module exposes two executable decision procedures over `FpPoly p`:
Berlekamp's rank criterion, phrased via the fixed-space matrix `Q_f - I`, and
Rabin's test, phrased via Frobenius remainders and gcd checks at the maximal
proper divisors of `deg f`.
-/
namespace Hex

namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-- `X^(p^k) - X` reduced modulo `f`. -/
def frobeniusDiffMod (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    FpPoly p :=
  FpPoly.frobeniusXPowMod f hmonic k - FpPoly.modByMonic f FpPoly.X hmonic

/--
Positive divisors of `n` below `n`, listed in ascending order.

These are the candidates from which Rabin's test extracts the maximal proper
divisors.
-/
def properDivisors (n : Nat) : List Nat :=
  ((List.range (n - 1)).map Nat.succ).filter fun d => n % d = 0

/--
The maximal proper divisors of `n`, i.e. those proper divisors not strictly
below any other proper divisor of `n`.
-/
def maximalProperDivisors (n : Nat) : List Nat :=
  let ds := properDivisors n
  ds.filter fun d => !(ds.any fun e => d < e && e % d = 0)

/-- `true` exactly when `g` is a nonzero constant polynomial. -/
def isUnitPolynomial (g : FpPoly p) : Bool :=
  match g.degree? with
  | some 0 => true
  | _ => false

/--
Berlekamp's executable rank criterion: a nonconstant monic `f` passes when
`rank(Q_f - I) = deg(f) - 1`.
-/
def berlekampRankTest (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] : Bool :=
  let n := basisSize f
  decide (0 < n ∧ Matrix.rref_rank (fixedSpaceMatrix f hmonic) = n - 1)

/--
The divisibility leg of Rabin's criterion: `f` divides `X^(p^n) - X`, with
`n = deg(f)`, exactly when the reduced remainder vanishes.
-/
def rabinDividesTest (f : FpPoly p) (hmonic : DensePoly.Monic f) : Bool :=
  let n := basisSize f
  (frobeniusDiffMod f hmonic n).isZero

/--
The gcd leg of Rabin's criterion at a single maximal proper divisor `d` of
`deg(f)`.
-/
def rabinCoprimeTest (f : FpPoly p) (hmonic : DensePoly.Monic f) (d : Nat) : Bool :=
  isUnitPolynomial (DensePoly.gcd f (frobeniusDiffMod f hmonic d))

/--
Record the per-divisor Rabin gcd checks so downstream factorization code can
see which maximal proper divisor rejected a candidate polynomial.
-/
def rabinWitnesses (f : FpPoly p) (hmonic : DensePoly.Monic f) : List (Nat × Bool) :=
  let n := basisSize f
  (maximalProperDivisors n).map fun d => (d, rabinCoprimeTest f hmonic d)

/--
Rabin's executable irreducibility test: `f` must be nonconstant, divide
`X^(p^n) - X`, and be coprime to `X^(p^d) - X` for every maximal proper
divisor `d` of `n = deg(f)`.
-/
def rabinTest (f : FpPoly p) (hmonic : DensePoly.Monic f) : Bool :=
  let n := basisSize f
  decide (0 < n) &&
    rabinDividesTest f hmonic &&
    (rabinWitnesses f hmonic).all Prod.snd

theorem berlekampRankTest_spec (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [Lean.Grind.Field (ZMod64 p)] :
    berlekampRankTest f hmonic = true ↔
      0 < basisSize f ∧
      Matrix.rref_rank (fixedSpaceMatrix f hmonic) = basisSize f - 1 := by
  simp [berlekampRankTest]

theorem rabinDividesTest_spec (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    rabinDividesTest f hmonic =
      (frobeniusDiffMod f hmonic (basisSize f)).isZero := by
  rfl

end Berlekamp

end Hex
