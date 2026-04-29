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

/-- Bezout evidence that one Rabin gcd leg is coprime. -/
structure RabinBezoutWitness (p : Nat) [ZMod64.Bounds p] where
  left : FpPoly p
  right : FpPoly p

/--
Self-describing certificate data for Rabin irreducibility checking.

The `bezout` array is indexed in the same order as `maximalProperDivisors
degree`.  Each witness proves coprimality of `f` and
`X^(p^d) - X mod f` by the executable identity
`left * f + right * (X^(p^d) - X) = 1`.
-/
structure IrreducibilityCertificate (p : Nat) [ZMod64.Bounds p] where
  prime : Nat
  degree : Nat
  powChain : Array (FpPoly p)
  bezout : Array (RabinBezoutWitness p)

namespace IrreducibilityCertificate

variable (cert : IrreducibilityCertificate p)

/-- Read the certified `X^(p^k) mod f` witness, if present. -/
def powWitness? (k : Nat) : Option (FpPoly p) :=
  cert.powChain[k]?

/-- Read the Bezout witness for the `i`-th maximal proper divisor, if present. -/
def bezoutWitness? (i : Nat) : Option (RabinBezoutWitness p) :=
  cert.bezout[i]?

end IrreducibilityCertificate

/-- The Rabin difference polynomial represented by a certificate pow-chain entry. -/
def certifiedFrobeniusDiffMod (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (powWitness : FpPoly p) : FpPoly p :=
  powWitness - FpPoly.modByMonic f FpPoly.X hmonic

/-- Check that a certificate's pow chain matches the committed Frobenius routine. -/
def checkPowChain (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate p) : Bool :=
  cert.powChain.size == cert.degree + 1 &&
    (List.range (cert.degree + 1)).all fun k =>
      cert.powChain[k]? == some (FpPoly.frobeniusXPowMod f hmonic k)

/-- Check one Bezout witness for a Rabin maximal-proper-divisor leg. -/
def checkRabinBezoutWitness (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate p) (i d : Nat) : Bool :=
  match cert.powChain[d]?, cert.bezout[i]? with
  | some powWitness, some witness =>
      let diff := certifiedFrobeniusDiffMod f hmonic powWitness
      witness.left * f + witness.right * diff == 1
  | _, _ => false

/-- Check all Bezout witnesses against `maximalProperDivisors cert.degree`. -/
def checkRabinBezoutWitnesses (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate p) : Bool :=
  let divisors := maximalProperDivisors cert.degree
  cert.bezout.size == divisors.length &&
    (divisors.zipIdx).all fun pair =>
      checkRabinBezoutWitness f hmonic cert pair.2 pair.1

/--
Executable checker for a Rabin irreducibility certificate.

It validates the self-described prime and degree, recomputes every pow-chain
entry, checks the divisibility leg `X^(p^n) = X mod f`, and verifies each
Bezout identity for the maximal proper divisors of `n`.
-/
def checkIrreducibilityCertificate (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate p) : Bool :=
  decide (cert.prime = p) &&
    decide (0 < cert.degree) &&
    decide (cert.degree = basisSize f) &&
    checkPowChain f hmonic cert &&
    (cert.powChain[cert.degree]? == some (FpPoly.modByMonic f FpPoly.X hmonic)) &&
    checkRabinBezoutWitnesses f hmonic cert

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

theorem checkPowChain_spec
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate p) :
    checkPowChain f hmonic cert = true →
      ∀ k, k ≤ cert.degree →
        cert.powChain[k]? = some (FpPoly.frobeniusXPowMod f hmonic k) := by
  sorry

theorem checkIrreducibilityCertificate_rabinTest
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate p) :
    checkIrreducibilityCertificate f hmonic cert = true →
      rabinTest f hmonic = true := by
  sorry

theorem checkIrreducibilityCertificate_irreducible_predicate
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate p) :
    checkIrreducibilityCertificate f hmonic cert = true →
      FpPoly.Irreducible f := by
  sorry

end Berlekamp

end Hex
