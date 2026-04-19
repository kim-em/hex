# hex-berlekamp-zassenhaus (the capstone)

Depends on hex-berlekamp + hex-hensel.

Complete factoring of univariate polynomials over `Z`.

This library should expose one stable public factoring API. The initial
implementation may use exhaustive recombination; later revisions may
replace or refine the recombination step using LLL, but that should
happen behind the same public interface rather than through a long-lived
strategy parameter.

The public API should accept arbitrary input polynomials and normalize
internally: extract content, remove powers of `X`, and reduce to the
primitive square-free case before running the Berlekamp-Zassenhaus
pipeline. The output is an `Array ZPoly` of primitive factors. Factor
order is operationally the array order, but the mathematical contract is
through product and membership rather than any semantic significance of
that order.

**Suggested top-level API:**
```lean
def factorWithBound (f : ZPoly) (B : Nat) : Array ZPoly
def factor (f : ZPoly) : Array ZPoly
```

`factorWithBound` is the core computational interface for conditional
correctness statements. `factor` is the default wrapper that computes and
uses the library's chosen coefficient bound internally.

**Prime selection sub-API:**
```lean
def isGoodPrime (f : ZPoly) (p : Nat) : Bool
def choosePrime (f : ZPoly) : Nat
```

`isGoodPrime` expresses the mathematical admissibility condition for the
modular reduction prime: at minimum `p ∤ lc(f)` and `f mod p` is
square-free. `choosePrime` is the default total heuristic chooser. It
should search through a small fixed number of admissible small primes,
factor `f mod p` for each, and choose the prime with the fewest modular
factors, breaking ties toward the smallest prime.

**Explicit pipeline records:**
```lean
structure PrimeChoiceData where
  p : Nat
  fModP : FpPoly p
  factorsModP : Array (FpPoly p)

structure LiftData where
  p : Nat
  k : Nat
  liftedFactors : Array ZPoly

structure RecombinationData where
  p : Nat
  k : Nat
  liftedFactors : Array ZPoly
```

Suggested stage helpers:
```lean
def choosePrimeData (f : ZPoly) : PrimeChoiceData
def henselLiftData (f : ZPoly) (B : Nat) (d : PrimeChoiceData) : LiftData
def recombine (f : ZPoly) (d : RecombinationData) : Array ZPoly
```

`recombine` is a named public helper. Its initial implementation may be
exhaustive subset recombination; a later LLL-based implementation should
refine the same interface rather than replacing it.

**Pipeline:**
1. Normalize `f` (content, powers of `X`, square-free part)
2. Choose a good prime `p` and factor `f mod p`
3. Hensel lift the modular factors to `mod p^k` for a sufficiently large
   bound-dependent `k`
4. Recombine lifted local factors into true factors in `Z[x]`

The exhaustive recombination path is acceptable as the initial
implementation. It is correct but exponential in the number of local
factors. LLL enters later at the recombination stage as an optimization
and eventual polynomial-time improvement, not as a separate public API.

**Conditional correctness (proved in this library, no Mathlib):**

The algorithm's correctness is proved conditionally on the coefficient
bound being valid. The key conditional theorem:
```lean
theorem factor_product_of_bound (f : ZPoly) (B : Nat)
    (hB : ∀ g : ZPoly, g ∣ f → ∀ i, |g.coeff i| ≤ B) :
    Array.foldl (· * ·) 1 (factorWithBound f B) = f
```

This library should also contain the computational invariants needed by
downstream stages, for example:
- `isGoodPrime` soundness with respect to the modular square-free
  preconditions needed by hex-berlekamp
- correctness of `choosePrimeData`
- correctness of the Hensel-lift stage under the explicit bound and prime
  data
- recombination product preservation under the lifted-factor hypotheses

These are computational pipeline theorems. The heavier abstract-algebraic
results remain in `hex-berlekamp-zassenhaus-mathlib`.

**Certificate structures for Z[x] irreducibility:**
```lean
structure ZPolyIrreducibilityCertificate where
  primes : Array Nat
  factorDegrees : Array (Array Nat)
  factorCerts : Array (Array IrreducibilityCertificate)
  -- Degree analysis data ruling out nontrivial factor degrees

def checkIrreducibleCert
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate) : Bool
```

The outer contract is checker-first: the precise internal certificate
layout may evolve, but the public contract should be stable.

Suggested soundness split:
- `hex-berlekamp-zassenhaus` proves the computational soundness of the
  checker data flow and degree-obstruction computation
- `hex-berlekamp-zassenhaus-mathlib` proves
  `checkIrreducibleCert f cert = true → Irreducible f`
