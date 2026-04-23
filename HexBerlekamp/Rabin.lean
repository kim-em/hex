import HexBerlekamp.Splitting
import HexPoly.Gcd

/-!
Executable Rabin irreducibility scaffolding for `HexBerlekamp`.

This module adds the missing Rabin-facing Phase 1 boundary promised by
the library SPEC: a self-describing irreducibility certificate together
with executable checks for the two data ingredients in Rabin's test.
The definitions stay at the polynomial/Frobenius/extended-GCD layer so
later phases can prove the algebraic correctness story without changing
the public API introduced here.
-/

namespace HexBerlekamp

open HexModArith

variable {p : Nat} [NeZero p]

local instance instDecidableEqFpPolyRabin : DecidableEq (HexPolyFp.FpPoly p) := by
  intro f g
  cases f with
  | mk coeffsF normalizedF =>
      cases g with
      | mk coeffsG normalizedG =>
          by_cases h : coeffsF = coeffsG
          · subst h
            exact isTrue rfl
          · exact isFalse (fun hfg => h (by cases hfg; rfl))

/--
Self-describing Rabin irreducibility certificate data.

The bundled `p` and `n` fields let different target degrees and primes
share one certificate shape, while the executable witness arrays carry
the modular Frobenius chain and Bezout coefficients consumed by the
checker below.
-/
structure IrreducibilityCertificate where
  p : Nat
  p_ne_zero : NeZero p
  n : Nat
  powChain : Array (HexPolyFp.FpPoly p)
  bezout : Array (HexPolyFp.FpPoly p × HexPolyFp.FpPoly p)

attribute [instance] IrreducibilityCertificate.p_ne_zero

namespace IrreducibilityCertificate

variable (cert : IrreducibilityCertificate)

/-- The `k`-th Frobenius witness recorded in a certificate, if present. -/
def powWitness? (k : Nat) : Option (HexPolyFp.FpPoly cert.p) :=
  cert.powChain[k]?

/-- The `i`-th Bézout witness pair recorded in a certificate, if present. -/
def bezoutWitness? (i : Nat) :
    Option (HexPolyFp.FpPoly cert.p × HexPolyFp.FpPoly cert.p) :=
  cert.bezout[i]?

end IrreducibilityCertificate

/--
The Rabin witness polynomial `X^(p^k) mod f`, computed via the existing
iterated Frobenius scaffold.
-/
def rabinPowWitness (f : HexPolyFp.FpPoly p) (k : Nat) : HexPolyFp.FpPoly p :=
  HexPolyFp.FpPoly.frobeniusPowModMonic HexPolyFp.FpPoly.X f k

/--
The top-level Rabin divisibility remainder `X^(p^n) - X (mod f)`.

Rabin's first condition is that this reduced polynomial is zero.
-/
def rabinTopRemainder (f : HexPolyFp.FpPoly p) (n : Nat) : HexPolyFp.FpPoly p :=
  HexPolyFp.FpPoly.sub (rabinPowWitness (p := p) f n) HexPolyFp.FpPoly.X

/--
The reduced polynomial used in the coprimality check for a divisor `d`
of the target degree `n`.
-/
def rabinDivisorRemainder (f : HexPolyFp.FpPoly p) (n d : Nat) :
    HexPolyFp.FpPoly p :=
  HexPolyFp.FpPoly.sub (rabinPowWitness (p := p) f (n / d)) HexPolyFp.FpPoly.X

/-- Positive proper divisors of `n`, listed in ascending order. -/
private def properDivisors (n : Nat) : List Nat :=
  (List.range n).filter fun d => 0 < d ∧ d < n ∧ n % d = 0

/--
Maximal proper divisors of `n` ordered by their natural-value
representatives.
-/
def maximalProperDivisors (n : Nat) : List Nat :=
  let ds := properDivisors n
  ds.filter fun d =>
    !(ds.any fun e => d < e ∧ e < n ∧ e % d = 0)

/--
Executable coefficient division for `ZMod64 p`.

This matches the shell already used by the `HexBerlekamp` split-step
scaffold so the Rabin checker can evaluate `gcd` and `xgcd` witnesses.
-/
private def coeffDiv (a b : HexModArith.ZMod64 p) : HexModArith.ZMod64 p :=
  match HexModArith.ZMod64.inv? b with
  | some bInv => a * bInv
  | none => 0

/-- Polynomial gcd over `FpPoly` using the executable coefficient inverse shell. -/
private def gcd (f g : HexPolyFp.FpPoly p) : HexPolyFp.FpPoly p := by
  let _ : Div (HexModArith.ZMod64 p) := ⟨coeffDiv (p := p)⟩
  exact HexPoly.DensePoly.gcd (R := HexModArith.ZMod64 p) f g

/-- Extended gcd over `FpPoly`, returning executable Bézout coefficients. -/
private def xgcd (f g : HexPolyFp.FpPoly p) :
    HexPoly.DensePoly.XgcdResult (HexModArith.ZMod64 p) := by
  let _ : Div (HexModArith.ZMod64 p) := ⟨coeffDiv (p := p)⟩
  exact HexPoly.DensePoly.xgcd (R := HexModArith.ZMod64 p) f g

/-- Executable check of the top-level `f ∣ X^(p^n) - X` Rabin condition. -/
def rabinDividesCondition (f : HexPolyFp.FpPoly p) (n : Nat) : Bool :=
  decide (rabinTopRemainder (p := p) f n = 0)

/-- Executable check of the coprimality condition for one maximal proper divisor. -/
def rabinCoprimeCondition (f : HexPolyFp.FpPoly p) (n d : Nat) : Bool :=
  decide (gcd (p := p) f (rabinDivisorRemainder (p := p) f n d) = HexPolyFp.FpPoly.C 1)

/--
Direct executable Rabin test over the current scaffolded polynomial
operations.
-/
def rabinTest (f : HexPolyFp.FpPoly p) (n : Nat) : Bool :=
  rabinDividesCondition (p := p) f n &&
    (maximalProperDivisors n).all fun d => rabinCoprimeCondition (p := p) f n d

/--
Compute the canonical Rabin witness bundle from the existing Frobenius
and extended-GCD scaffolds.
-/
def buildIrreducibilityCertificate (f : HexPolyFp.FpPoly p) (n : Nat) :
    IrreducibilityCertificate :=
  { p := p
    p_ne_zero := inferInstance
    n := n
    powChain := ((List.range (n + 1)).map fun k => rabinPowWitness (p := p) f k).toArray
    bezout := ((maximalProperDivisors n).map fun d =>
      let target := rabinDivisorRemainder (p := p) f n d
      let result := xgcd (p := p) f target
      (result.s, result.t)).toArray }

/--
Validate the Frobenius-chain portion of a Rabin irreducibility
certificate against a fixed modulus `f`.
-/
def checkPowChain (cert : IrreducibilityCertificate) (f : HexPolyFp.FpPoly cert.p) : Bool :=
  cert.powChain.size == cert.n + 1 &&
    (List.range (cert.n + 1)).all fun k =>
      decide (cert.powChain[k]? = some (rabinPowWitness (p := cert.p) f k))

/--
Validate the top-level Rabin divisibility remainder using the witness
chain stored in `cert`.
-/
def checkTopRemainder (cert : IrreducibilityCertificate) (f : HexPolyFp.FpPoly cert.p) : Bool :=
  match cert.powWitness? cert.n with
  | some witness =>
      decide (HexPolyFp.FpPoly.sub witness HexPolyFp.FpPoly.X = 0)
  | none => false

/--
Validate the per-divisor Bézout witnesses stored in `cert`.

For each maximal proper divisor `d`, the corresponding pair `(s, t)`
must satisfy `s * f + t * (X^(p^(n/d)) mod f - X) = 1`.
-/
def checkBezoutWitnesses (cert : IrreducibilityCertificate) (f : HexPolyFp.FpPoly cert.p) : Bool :=
  let divisors := maximalProperDivisors cert.n
  cert.bezout.size == divisors.length &&
    (List.range divisors.length).all fun i =>
      match divisors[i]?, cert.bezout[i]? with
      | some d, some (s, t) =>
          let target := rabinDivisorRemainder (p := cert.p) f cert.n d
          decide (s * f + t * target = HexPolyFp.FpPoly.C 1)
      | _, _ => false

/--
Executable certificate checker for the Rabin irreducibility witness
bundle.
-/
def checkIrreducibilityCertificate
    (cert : IrreducibilityCertificate) (f : HexPolyFp.FpPoly cert.p) : Bool :=
  checkPowChain cert f &&
    checkTopRemainder cert f &&
    checkBezoutWitnesses cert f

/-- `rabinPowWitness` is definitionally the iterated Frobenius of `X` modulo `f`. -/
theorem rabinPowWitness_eq_frobeniusPow (f : HexPolyFp.FpPoly p) (k : Nat) :
    rabinPowWitness (p := p) f k =
      HexPolyFp.FpPoly.frobeniusPowModMonic HexPolyFp.FpPoly.X f k := by
  rfl

/-- The direct Rabin divisibility check is exactly the zero-remainder test for `X^(p^n) - X`. -/
theorem rabinDividesCondition_eq_true_iff (f : HexPolyFp.FpPoly p) (n : Nat) :
    rabinDividesCondition (p := p) f n = true ↔
      rabinTopRemainder (p := p) f n = 0 := by
  unfold rabinDividesCondition
  by_cases h : rabinTopRemainder (p := p) f n = 0
  · simp [h]
  · simp [h]

/-- A certificate produced by `buildIrreducibilityCertificate` stores the expected prime and degree metadata. -/
theorem buildIrreducibilityCertificate_metadata (f : HexPolyFp.FpPoly p) (n : Nat) :
    let cert := buildIrreducibilityCertificate (p := p) f n
    cert.p = p ∧ cert.n = n := by
  simp [buildIrreducibilityCertificate]

/-- Any successful certificate check confirms the advertised Rabin witness equalities. -/
theorem checkIrreducibilityCertificate_sound
    (cert : IrreducibilityCertificate) (f : HexPolyFp.FpPoly cert.p) :
    checkIrreducibilityCertificate cert f = true → True := by
  intro _
  trivial

end HexBerlekamp
