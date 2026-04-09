# hex-berlekamp-zassenhaus (the capstone)

Depends on hex-berlekamp + hex-hensel + hex-lll.

Complete polynomial-time factoring of univariate polynomials over Z.

**Pipeline:**
1. `f` → `squareFreePart(f)` (Yun's algorithm, from hex-poly-z)
2. Choose prime `p` not dividing `disc(f)`, with `f mod p` square-free
3. `f mod p` → irreducible factors `g₁, ..., gᵣ mod p` (hex-berlekamp)
4. Hensel lift to `mod p^k` for Mignotte-bounded `k` (hex-hensel)
5. Recombine subsets of lifted factors to find true `Z[x]` factors
6. Step 5 uses LLL for polynomial-time recombination (hex-lll)

**Without LLL** (Phase 1): exponential-time subset recombination. Still
correct, just slow for high-degree polynomials with many factors mod p.

**With LLL** (Phase 2): polynomial-time recombination. Short lattice
vectors correspond to true factors.

**Conditional correctness (proved in this library, no Mathlib):**

The algorithm's correctness is proved conditionally on the coefficient
bound being valid. The key conditional theorem:
```lean
theorem factor_product_of_bound (f : ZPoly) (B : Nat)
    (hB : ∀ g : ZPoly, g ∣ f → ∀ i, |g.coeff i| ≤ B) :
    (factor f B).prod = f
```
This keeps the heavy algorithmic verification Mathlib-free. The only
piece that needs Mathlib is proving that the Mignotte bound is valid
(which requires the Fundamental Theorem of Algebra).

**Certificate structures for Z[x] irreducibility:**
```lean
structure ZPolyIrreducibilityCertificate where
  primes : Array Nat
  factorDegrees : Array (Array Nat)
  factorCerts : Array (Array IrreducibilityCertificate)
  -- Degree analysis: intersection of subset sums = {0, deg(f)}
```
