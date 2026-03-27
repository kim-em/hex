# lean-algebra — Verified Computational Algebra in Lean 4

A collection of cooperating Lean 4 libraries providing performant, verified
algorithms for computational algebra: polynomial arithmetic, factoring,
irreducibility testing, lattice basis reduction, and related tools.

## Design principles

1. **Many small libraries**, not one monolith. Each bullet in the overview is
   its own Lake package with its own repo.

2. **No Mathlib in the computational core.** Every library that computes
   something is Mathlib-free. Separate bridge libraries depend on both the
   computational library and Mathlib to provide the verification layer
   (proving the computation corresponds to the mathematical specification).

3. **Performant by default.** Dense array-backed representations, `UInt64`
   coefficients for `F_p`, Barrett/Montgomery reduction for modular
   arithmetic. FFI to FLINT as an optional fast path where it matters.

4. **Swappable polynomial representations.** A typeclass interface lets
   algorithms work over any representation (dense, sparse sorted, sparse
   hashmap). But the default — and the one everything is tested and proved
   against first — is dense `Array`-backed.

5. **Certificate-based verification where possible.** For irreducibility:
   SageMath generates a certificate, Lean validates it. The certificate
   checker is small and fully verified. The algorithm that *finds* the
   certificate is verified separately (and more ambitiously).

6. **Clear DAG structure.** Libraries can be developed in parallel. LLL has
   no dependency on polynomial arithmetic. Hensel lifting is independent of
   LLL. Everything meets at the top (Berlekamp-Zassenhaus).

---

## Library DAG

```
                    lean-berlekamp-zassenhaus
                   (complete Z[x] factoring)
                  /            |            \
                 /             |             \
    lean-berlekamp    lean-hensel    lean-lll
    (F_p factoring)   (lifting)     (lattice reduction)
         |                |              |
         |                |              |
    lean-poly-fp     lean-poly-z    lean-lattice
    (poly over F_p)  (poly over Z)  (integer vectors/matrices)
         |                |              |
         +-------+--------+              |
                 |                        |
            lean-poly                     |
            (poly interface +             |
             dense repr)                  |
                 |                        |
            lean-mod-arith           lean-matrix
            (modular arithmetic)     (dense integer matrices)
                 |                        |
                 +----------+-------------+
                            |
                       lean-arith
                       (UInt64/Int arithmetic,
                        Barrett reduction,
                        extended GCD for integers)
```

**Bridge libraries** (depend on Mathlib + computational library):

```
    lean-berlekamp-zassenhaus-mathlib
    lean-berlekamp-mathlib
    lean-hensel-mathlib
    lean-lll-mathlib
    lean-poly-mathlib          (proves dense repr ≅ Polynomial R)
    lean-mod-arith-mathlib     (proves ZMod64 ≅ ZMod p)
```

Each bridge library proves that the computational library's operations
correspond to the Mathlib-defined mathematical objects. Theorems live in
the bridge; algorithms live in the core.

---

## Library descriptions

### lean-arith (foundation, no dependencies)

Core integer arithmetic that everything else builds on.

**Contents:**
- `UInt64` extended GCD
- Barrett reduction for modular multiplication (precomputed inverse)
- Montgomery multiplication (for sustained modular arithmetic)
- `Int` extended GCD
- Mignotte bound computation (coefficient bounds for polynomial factors)
- Cauchy root bound

**Key properties:**
- `extGcd a b = (g, s, t)` implies `s * a + t * b = g` and `g = gcd a b`
- Barrett reduction: `barrettMul a b p pinv = (a * b) % p`
- These are characterizing — they describe the *what*, not the *how*

**No Mathlib needed.** Everything is `Nat`, `Int`, `UInt64`.

---

### lean-matrix (foundation, no dependencies beyond lean-arith)

Dense integer matrices and vectors.

**Contents:**
- `Matrix n m Int` as `Array (Array Int)` with dimension proofs
- `Vector n Int` as `Array Int` with size proof
- Matrix-vector multiplication
- Dot product, norm squared
- Determinant (for lattice volume)
- Row operations (swap, add multiple of one row to another)

**Key properties:**
- Row operations preserve determinant (up to sign)
- `det (rowSwap M i j) = -det M`
- Dot product is bilinear

**No Mathlib needed.** Pure array operations with `Int`.

---

### lean-mod-arith (modular arithmetic, depends on lean-arith)

Arithmetic in `Z/nZ` with `UInt64`-backed coefficients.

**Contents:**
- `ZMod64 (p : Nat)` — a `UInt64` with proof `val < p`
- Addition, subtraction, multiplication with Barrett/Montgomery reduction
- Inversion via extended GCD (for prime moduli)
- Exponentiation by squaring
- `ZMod64` instances: `Add`, `Mul`, `Neg`, `Inv`, `BEq`, `DecidableEq`

**Key properties:**
- Ring axioms: `a * (b + c) = a * b + a * c`, etc.
- `inv a * a = 1` when `gcd a p = 1`
- `pow a (p-1) = 1` when `p` is prime (Fermat's little theorem — but
  proved computationally, not via Mathlib's abstract algebra)

**No Mathlib needed.** The ring axioms can be proved directly from the
modular arithmetic definitions.

---

### lean-mod-arith-mathlib (bridge, depends on lean-mod-arith + Mathlib)

Proves `ZMod64 p ≅ ZMod p` as rings. This means any theorem proved about
`ZMod p` in Mathlib applies to `ZMod64 p`, and any computation done with
`ZMod64 p` is known to be correct in the mathematical sense.

**Key theorem:**
```lean
def equiv : ZMod64 p ≃+* ZMod p
```

---

### lean-poly (polynomial interface + dense representation, depends on lean-arith)

The core polynomial library. Defines both the typeclass interface and the
default dense representation.

**Typeclass interface:**
```lean
class PolyOps (P : Type*) (R : outParam Type*) where
  zero : P
  one : P
  X : P
  C : R → P
  add : P → P → P
  neg : P → P
  mul : P → P → P
  degree : P → Nat
  coeff : P → Nat → R
  leadingCoeff : P → R
  divMod : P → P → P × P
  eval : P → R → R
  ofCoeffs : Array R → P
  toCoeffs : P → Array R
```

**Dense representation:**
```lean
structure DensePoly (R : Type*) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ 0
```

The normalization invariant (no trailing zeros) ensures structural equality
= semantic equality. Every operation maintains this invariant.

**Operations implemented:**
- Addition, subtraction, multiplication (schoolbook, Karatsuba for large degree)
- Division with remainder (for monic divisors; general division over fields)
- Polynomial GCD (Euclidean algorithm)
- Extended GCD (Bezout coefficients: `a*f + b*g = gcd(f,g)`)
- Evaluation (Horner's method)
- Composition, derivative
- Content and primitive part (for `DensePoly Int`)

**Polynomial GCD — key properties:**
- `gcd f g` divides both `f` and `g`
- Every common divisor of `f` and `g` divides `gcd f g`
- Bezout: `∃ a b, a * f + b * g = gcd f g`
- These are characterizing properties, not tautological

**Representations (Phase 2, optional):**

Sparse sorted array:
```lean
structure SparsePoly (R : Type*) [Zero R] [DecidableEq R] where
  terms : Array (Nat × R)
  sorted : terms.toList.Pairwise (fun a b => a.1 < b.1)
  nonzero : ∀ t ∈ terms.toList, t.2 ≠ 0
```

Sparse hashmap (for exploration, not primary):
```lean
structure HashPoly (R : Type*) [Zero R] [BEq R] [Hashable Nat] where
  terms : HashMap Nat R
  nonzero : ∀ k v, terms.find? k = some v → v ≠ 0
```

The wrapper-without-zeros pattern: a raw representation that allows zeros
(for efficient intermediate computation) and a normalized wrapper that
strips them (for equality and storage). Operations work on the raw type
internally and normalize on output.

**No Mathlib needed.**

---

### lean-poly-mathlib (bridge, depends on lean-poly + Mathlib)

Proves `DensePoly R ≅ Polynomial R` as rings (where `Polynomial R` is
Mathlib's `AddMonoidAlgebra R ℕ` backed by `Finsupp`).

**Key theorems:**
```lean
def equiv : DensePoly R ≃+* Polynomial R

theorem gcd_spec (f g : DensePoly R) [Field R] :
    equiv (DensePoly.gcd f g) = Polynomial.gcd (equiv f) (equiv g)

theorem extGcd_bezout (f g : DensePoly R) [Field R] :
    let (a, b, d) := DensePoly.extGcd f g
    equiv a * equiv f + equiv b * equiv g = equiv d
```

---

### lean-poly-fp (polynomials over F_p, depends on lean-poly + lean-mod-arith)

Specialized polynomial arithmetic over `Z/pZ` using `UInt64` coefficients.

**Contents:**
- `FpPoly p` = `DensePoly (ZMod64 p)` with specialized fast paths
- Frobenius map: `X^p mod f` via repeated squaring
- `X^(p^k) mod f` for arbitrary k (square-and-multiply on polynomials)
- Modular composition (evaluate one polynomial at another, mod a third)
- Square-free decomposition (Yun's algorithm adapted for `F_p`)

**Key properties:**
- Frobenius endomorphism: `frob(a + b) = frob(a) + frob(b)`
- Square-free decomposition: the output factors are pairwise coprime, their
  product equals the input, and each factor is square-free

**No Mathlib needed.** The modular arithmetic is from lean-mod-arith.

For `GF(2)` specifically, consider a packed bitwise representation:
```lean
structure GF2Poly where
  words : Array UInt64
  degree : Nat
  -- bit at position `degree` is 1 (unless zero polynomial)
```
Addition = XOR, multiplication uses carry-less multiply. This is a
64x speedup for `F_2` polynomials, important for coding theory.

---

### lean-poly-z (polynomials over Z, depends on lean-poly)

Specialized polynomial arithmetic over `Z`.

**Contents:**
- `ZPoly` = `DensePoly Int`
- Content and primitive part: `f = content(f) * primitivePart(f)`
- Gauss's lemma (computational version): the product of primitive
  polynomials is primitive
- Mignotte bound: coefficient bound for factors of `f`
- Reduction modulo p: `ZPoly → FpPoly p`

**Key properties:**
- `content(f * g) = content(f) * content(g)` (Gauss)
- `primitivePart(f)` is primitive (content = 1)
- Mignotte bound is valid: any factor of `f` has coefficients bounded by
  the computed bound

**No Mathlib needed** for the computations. Gauss's lemma can be proved
from first principles (it's essentially about GCD of integers).

---

### lean-berlekamp (factoring over F_p, depends on lean-poly-fp)

Berlekamp's algorithm and Rabin's irreducibility test for polynomials
over finite fields.

**Contents:**
- **Berlekamp matrix construction**: compute `Q_f`, the matrix of the
  Frobenius map `h ↦ h^p mod f` in the basis `{1, x, ..., x^{n-1}}`
- **Berlekamp kernel**: nullspace of `Q_f - I`
- **Irreducibility test**: `f` is irreducible iff `rank(Q_f - I) = n - 1`
- **Factoring**: elements of the kernel split `f` via `gcd(f, h - c)`
  for `c ∈ F_p`
- **Rabin's test**: `f` is irreducible iff `f | X^(p^n) - X` and
  `gcd(f, X^(p^(n/d)) - X) = 1` for each maximal proper divisor `d` of `n`
- **Distinct-degree factorization**: separate factors by degree

**Certificate mode:**
Given a polynomial `f` over `F_p`, produce an `IrreducibilityCertificate`:
```lean
structure IrreducibilityCertificate (p n : Nat) where
  -- Square-and-multiply witnesses for X^(p^k) mod f
  powChain : Array (FpPoly p)
  -- Bezout coefficients for coprimality at each maximal divisor
  bezout : Array (FpPoly p × FpPoly p)
  -- Proof obligations (all decidable):
  -- powChain validates the square-and-multiply computation
  -- bezout witnesses prove gcd(f, X^(p^(n/d)) - X) = 1
```

The certificate checker is tiny and fully verified. SageMath generates
certificates; Lean validates them. This gives verified irreducibility
results immediately, before the full algorithm is proved correct.

**Key properties (characterizing):**

Rabin's test:
```lean
theorem rabin_irreducible (f : FpPoly p) (hf : f.degree = n) :
    rabinTest f = true ↔
    Irreducible f
```

Berlekamp:
```lean
theorem berlekamp_complete (f : FpPoly p) (hf : squareFree f) :
    (berlekampFactor f).prod = f ∧
    ∀ g ∈ berlekampFactor f, Irreducible g
```

**No Mathlib needed** for the algorithm. The bridge library connects
`Irreducible` in the computational sense to Mathlib's `Irreducible`.

---

### lean-berlekamp-mathlib (bridge)

Connects the computational `Irreducible` (no proper factorization exists
in the `FpPoly` type) to Mathlib's `Irreducible` in `Polynomial (ZMod p)`.

**Key theorem:**
```lean
theorem berlekamp_irreducible_iff (f : FpPoly p) :
    Berlekamp.Irreducible f ↔
    _root_.Irreducible (lean-poly-mathlib.equiv f : Polynomial (ZMod p))
```

This is the payoff: a `Decidable` instance for `Irreducible` on
`Polynomial (ZMod p)`, backed by a verified algorithm.

---

### lean-hensel (Hensel lifting, depends on lean-poly-fp + lean-poly-z)

Lifts a factorization of `f mod p` to a factorization of `f mod p^k`.

**Contents:**
- **Linear Hensel lifting**: from `mod p^k` to `mod p^(k+1)`
  - Given `f ≡ g * h (mod p^k)` with `gcd(g,h) = 1 mod p`
  - Compute `e = (f - g*h) / p^k`
  - Distribute `e` between `g` and `h` using Bezout cofactors
  - Produce `g', h'` with `f ≡ g' * h' (mod p^(k+1))`
- **Quadratic Hensel lifting**: from `mod p^k` to `mod p^(2k)` (doubling)
  - Same idea but lifts the Bezout cofactors simultaneously
  - `log₂(k)` steps instead of `k-1`
- **Multifactor lifting**: binary factor tree approach
  - Build a balanced tree of partial products
  - Apply binary lifting at each internal node
- **Mignotte bound**: compute the required `k` such that `p^k` exceeds
  the coefficient bound for any true factor

**Key properties:**
```lean
-- Correctness
theorem hensel_correct (f g h : ZPoly) (p k : Nat) :
    let (g', h') := henselLift f g h p k
    g' * h' ≡ f [MOD p^(k+1)]

-- Extension
theorem hensel_extends (f g h : ZPoly) (p k : Nat) :
    let (g', h') := henselLift f g h p k
    g' ≡ g [MOD p^k] ∧ h' ≡ h [MOD p^k]

-- Degree preservation
theorem hensel_degree (f g h : ZPoly) (p k : Nat) :
    let (g', h') := henselLift f g h p k
    g'.degree = g.degree ∧ h'.degree = h.degree

-- Uniqueness (the deep theorem)
theorem hensel_unique (f g h g' h' : ZPoly) (p k : Nat) :
    g.leadingCoeff = 1 →
    g * h ≡ f [MOD p^k] → g' * h' ≡ f [MOD p^k] →
    g ≡ g' [MOD p] → h ≡ h' [MOD p] →
    coprime_mod g h p →
    g = g' ∧ h = h'
```

**Strategy**: Start with linear lifting (simpler invariant, easier to
verify). Add quadratic as an optimization proved equivalent via uniqueness.
This mirrors the Isabelle approach.

**No Mathlib needed.** Modular arithmetic on `Int` polynomials.

---

### lean-lll (LLL lattice basis reduction, depends on lean-matrix)

**Completely independent of the polynomial libraries.** Can be developed
in parallel from day one.

**Contents:**
- Classical LLL algorithm with exact rational arithmetic
- Integer-only variant (d-representation, avoids explicit rationals)
- Gram-Schmidt orthogonalization (exact, not floating-point)
- Size reduction (ensure |μ_{i,j}| ≤ 1/2)
- Lovász condition check and basis swap

**The algorithm:**
```
Input:  basis b_1, ..., b_n ∈ Z^m, parameter δ ∈ (1/4, 1]
Output: LLL-reduced basis for the same lattice

Maintain GSO: b*_i and μ_{i,j} = ⟨b_i, b*_j⟩ / ⟨b*_j, b*_j⟩

k := 2
while k ≤ n:
  Size-reduce b_k: for j = k-1 downto 1, subtract round(μ_{k,j}) * b_j
  If Lovász condition holds (|b*_k|² ≥ (δ - μ²_{k,k-1}) · |b*_{k-1}|²):
    k := k + 1
  Else:
    swap b_k and b_{k-1}, update GSO
    k := max(k-1, 2)
```

**Termination proof:**
- Potential function: `D = ∏ᵢ |b*ᵢ|^{2(n-i)}`
- D is a positive integer (since basis vectors are in Z^m)
- Each swap decreases D by factor ≥ δ
- Size reduction does not change D
- Therefore: at most `n(n-1)/2 · log(B) / log(1/δ)` swaps, where B =
  max input vector norm squared. This is the polynomial running time bound.

**d-representation** (the Isabelle approach, avoids rationals):
Instead of storing μ_{i,j} as rationals, store `d_{i+1} · μ_{i,j}` where
`d_i = det(Gram matrix of first i vectors)`. All d_i are positive integers.
All operations become integer-only. No GCD, no fraction normalization.
This is what makes LLL performant in a proof assistant.

**Key properties (all characterizing):**

```lean
-- Lattice preservation
theorem lll_same_lattice (b : Basis) (δ : Rat) :
    lattice (lll b δ) = lattice b

-- LLL-reducedness
theorem lll_reduced (b : Basis) (δ : Rat) :
    isLLLReduced (lll b δ) δ

-- Short vector guarantee
theorem lll_short_vector (b : Basis) (δ : Rat) (v : Vector) :
    v ∈ lattice b → v ≠ 0 →
    ‖(lll b δ).head‖² ≤ α^(n-1) * ‖v‖²
  where α := 1 / (δ - 1/4)

-- Polynomial swap count
theorem lll_swap_bound (b : Basis) (δ : Rat) :
    swapCount (lll b δ) ≤ n * (n-1) / 2 * log₂(maxNormSq b) / log₂(1/δ)
```

The short vector guarantee with `δ = 3/4` gives `‖b₁‖ ≤ 2^{(n-1)/2} · λ₁`,
where λ₁ is the shortest vector in the lattice. This is a mathematical
theorem, not a tautology.

**No Mathlib needed** for the algorithm or the basic properties.
Lean's built-in `Int` and `Rat` suffice.

---

### lean-lll-mathlib (bridge)

Connects `lean-lll` to Mathlib's linear algebra. Proves:
- The lattice in the computational sense corresponds to a `Submodule ℤ`
- The GSO corresponds to Mathlib's `gramSchmidt`
- The short vector bound holds with respect to Mathlib's `norm`

---

### lean-berlekamp-zassenhaus (the capstone, depends on lean-berlekamp + lean-hensel + lean-lll)

Complete polynomial-time factoring of univariate polynomials over Z.

**Pipeline:**
1. `f` → `squareFreePart(f)` (Yun's algorithm, from lean-poly-z)
2. `squareFreePart(f)` → choose prime `p` not dividing `disc(f)`
3. `f mod p` → irreducible factors `g₁, ..., gᵣ mod p` (lean-berlekamp)
4. Hensel lift `g₁, ..., gᵣ` to `mod p^k` for Mignotte-bounded `k` (lean-hensel)
5. Recombine subsets of lifted factors to find true `Z[x]` factors
6. Step 5 uses LLL for polynomial-time recombination (lean-lll)

**Without LLL** (Phase 1): exponential-time recombination (try all
subsets). Still correct, just slow for high-degree polynomials with
many factors mod p. This is the "Berlekamp-Zassenhaus" algorithm.

**With LLL** (Phase 2): polynomial-time recombination. The lattice is
constructed from Hensel-lifted factors and the Mignotte bound. Short
vectors correspond to true factors.

**Key properties:**
```lean
-- Correctness: output factors multiply to input
theorem factor_product (f : ZPoly) :
    (factor f).prod = f

-- Irreducibility: each output factor is irreducible
theorem factor_irreducible (f : ZPoly) :
    ∀ g ∈ factor f, Irreducible g

-- Completeness: the factorization is unique (up to order and units)
theorem factor_unique (f : ZPoly) (gs hs : List ZPoly) :
    gs.prod = f → hs.prod = f →
    (∀ g ∈ gs, Irreducible g) → (∀ h ∈ hs, Irreducible h) →
    gs ~ hs  -- multiset equality up to associates
```

**Certificate mode for Z[x] irreducibility:**
```lean
structure ZPolyIrreducibilityCertificate where
  -- Primes used for modular factoring
  primes : Array Nat
  -- For each prime: factor degrees
  factorDegrees : Array (Array Nat)
  -- For each factor: irreducibility certificate over F_p
  factorCerts : Array (Array (IrreducibilityCertificate ...))
  -- Degree analysis: intersection of subset sums = {0, deg(f)}
```

Alternatively, an LPFW (Large Prime Factor Witness) certificate:
```lean
structure LPFWCertificate where
  evalPoint : Int           -- m such that |f(m)| has a large prime factor
  prime : Nat               -- the large prime P dividing |f(m)|
  quotient : Nat            -- |f(m)| / P
  cauchyBound : Rat         -- root bound ρ
  degreeBound : Nat         -- d from degree analysis
  -- Verification: P is prime, f(m) = ±quotient * P, quotient < (|m| - ρ)^d
```

---

### Practical applications

**Cryptographic field construction:**
To build `GF(2^128)` for AES, you need an irreducible polynomial of
degree 128 over `F_2`. With lean-berlekamp + certificate mode, you can
produce a Lean proof that `x^128 + x^7 + x^2 + x + 1` is irreducible
over `F_2`.

**Coding theory:**
Reed-Solomon and BCH codes need irreducible polynomials over finite
fields. The generator polynomial must divide `x^n - 1` over `F_q`.
Verified factoring provides certified generator polynomials.

**Number theory:**
Computing rings of integers requires factoring polynomials over Z and
testing irreducibility. This is what the Baanen et al. project needs
(and currently delegates to SageMath with unverified certificates).

**Cryptanalysis:**
LLL is the core tool for lattice-based attacks (Coppersmith's method
for RSA, knapsack attacks). A verified LLL gives confidence in
attack results.

---

## Dependency DAG (for parallel development)

```
Phase 0 (all parallel, no dependencies between them):
  ├── lean-arith
  ├── lean-matrix
  └── (lean-poly can start with inline arith)

Phase 1 (each depends only on Phase 0):
  ├── lean-mod-arith          (← lean-arith)
  ├── lean-poly               (← lean-arith)
  ├── lean-lll                (← lean-matrix)
  └── lean-lattice            (← lean-matrix)

Phase 2 (each depends on Phase 1):
  ├── lean-poly-fp            (← lean-poly + lean-mod-arith)
  ├── lean-poly-z             (← lean-poly)
  └── lean-lll is complete    (independent)

Phase 3 (each depends on Phase 2):
  ├── lean-berlekamp          (← lean-poly-fp)
  └── lean-hensel             (← lean-poly-fp + lean-poly-z)

Phase 4 (the capstone):
  └── lean-berlekamp-zassenhaus (← lean-berlekamp + lean-hensel + lean-lll)

Bridge libraries (can start whenever their computational lib is ready):
  ├── lean-mod-arith-mathlib  (← lean-mod-arith + Mathlib, Phase 1+)
  ├── lean-poly-mathlib       (← lean-poly + Mathlib, Phase 1+)
  ├── lean-berlekamp-mathlib  (← lean-berlekamp + Mathlib, Phase 3+)
  ├── lean-hensel-mathlib     (← lean-hensel + Mathlib, Phase 3+)
  └── lean-lll-mathlib        (← lean-lll + Mathlib, Phase 1+)
```

**Key insight:** LLL is completely independent of the polynomial pipeline.
It can be developed from day one in parallel with everything else. The
only point of contact is at the very top (Berlekamp-Zassenhaus), where LLL
is used for polynomial-time factor recombination.

---

## Session estimates

| Library | Sessions | Dependencies | Parallel? |
|---------|----------|--------------|-----------|
| lean-arith | 3-5 | None | Yes |
| lean-matrix | 3-5 | None | Yes |
| lean-mod-arith | 3-5 | lean-arith | Yes (with lean-poly) |
| lean-poly | 5-8 | lean-arith | Yes (with lean-mod-arith) |
| lean-lll | 8-12 | lean-matrix | Yes (with everything) |
| lean-poly-fp | 3-5 | lean-poly, lean-mod-arith | — |
| lean-poly-z | 3-5 | lean-poly | Yes (with lean-poly-fp) |
| lean-berlekamp | 5-8 | lean-poly-fp | — |
| lean-hensel | 5-8 | lean-poly-fp, lean-poly-z | Yes (with lean-berlekamp) |
| lean-berlekamp-zassenhaus | 5-8 | lean-berlekamp, lean-hensel, lean-lll | — |
| Bridge libraries (total) | 10-15 | Various + Mathlib | Yes (each independent) |

**Total: ~55-85 sessions.**

### Milestones

**M1 (~15 sessions):** lean-arith + lean-poly + lean-mod-arith working.
Can do polynomial arithmetic over Z and F_p. GCD, extended GCD, division.
Conformance-tested against SageMath.

**M2 (~25 sessions, parallel with M1):** lean-matrix + lean-lll working.
LLL reduces lattice bases with verified short vector guarantee.

**M3 (~15 sessions after M1):** lean-berlekamp working. Can factor
polynomials over F_p and test irreducibility. Certificate mode operational.

**M4 (~10 sessions after M1):** lean-hensel working. Can lift factorizations
from F_p to Z/p^kZ.

**M5 (~8 sessions after M2+M3+M4):** lean-berlekamp-zassenhaus. Complete
verified polynomial factoring over Z.

**M6 (ongoing):** Bridge libraries connecting to Mathlib. `Decidable`
instance for `Irreducible` on `Polynomial (ZMod p)`.

---

## Polynomial representation design

### Primary: Dense (Array-backed)

```lean
structure DensePoly (R : Type*) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ 0
```

- Index = degree, `coeffs[i]` is the coefficient of `x^i`
- Normalization invariant: no trailing zeros
- Structural equality = semantic equality (critical for proofs)
- O(1) degree, O(1) coefficient access

### Secondary: Sparse sorted (Array of pairs)

```lean
structure SparsePoly (R : Type*) [Zero R] [DecidableEq R] where
  terms : Array (Nat × R)
  sorted : ∀ i j, i < j → i < terms.size → j < terms.size →
           (terms[i]).1 < (terms[j]).1
  nonzero : ∀ i, i < terms.size → (terms[i]).2 ≠ 0
```

### Tertiary: Sparse hashmap

```lean
structure HashPoly (R : Type*) [Zero R] [BEq R] [Hashable Nat] where
  map : HashMap Nat R
  -- No extensional equality without conversion to sorted form
```

### The typeclass

```lean
class PolyRepr (P : Type*) (R : outParam Type*) extends
    Add P, Mul P, Neg P, Zero P, One P, BEq P where
  degree : P → Nat
  coeff : P → Nat → R
  ofCoeffs : Array R → P
  -- Extensionality: two polynomials are equal iff all coefficients agree
  ext : ∀ p q : P, (∀ i, coeff p i = coeff q i) → p = q
```

Algorithms are written against `PolyRepr`. Concrete instances are provided
for `DensePoly`, `SparsePoly`, `HashPoly`. Performance-critical code can
specialize to `DensePoly` with `@[specialize]`.

### Zero-value wrapper pattern

For internal computation, allow zeros (faster, no normalization overhead):

```lean
structure RawDensePoly (R : Type*) where
  coeffs : Array R
  -- No normalization invariant. Fast for intermediate computation.
```

Normalize on output:

```lean
def RawDensePoly.normalize [Zero R] [DecidableEq R]
    (p : RawDensePoly R) : DensePoly R :=
  let coeffs := p.coeffs.popWhile (· == 0)
  ⟨coeffs, ...⟩
```

This gives the best of both worlds: fast intermediate arithmetic (no
trailing-zero checks on every operation) with clean equality on final
results.

---

## Prior art

**Isabelle/HOL** (the gold standard): The Innsbruck group (Thiemann,
Divasón, Joosten, Yamada) verified the entire Berlekamp-Zassenhaus + LLL
pipeline. Degree-500 polynomials factor at 2.5x Mathematica speed. ~44K
lines of Isabelle across multiple AFP entries.

**Baanen et al. (Lean 4)**: Certificate-based irreducibility checking for
the rings-of-integers project. Uses `decide`/`native_decide` on list-based
polynomials. Works but doesn't scale beyond small degrees.

**CoqEAL (Coq)**: Verified Karatsuba, Strassen, Bareiss, Smith normal form.
Refinement-based approach (abstract spec → concrete implementation).

**FLINT (C)**: The performance target. Dense `nmod_poly` and `fmpz_poly`
with Barrett reduction, Karatsuba, Kronecker segmentation, NTT. Not
verified but extremely well-tested.

---

## What verification buys you

For standalone crypto primitive verification, the honest answer is "not
much beyond what HACL* already provides." But computational algebra is
different:

1. **Results depend on algorithms being correct.** If SageMath says
   `x^128 + x^7 + x^2 + x + 1` is irreducible over `F_2`, how do you
   know? You trust SageMath. With verified certificates, you trust the
   Lean kernel.

2. **The properties are characterizing.** Rabin's theorem, the Lovász
   condition, Hensel uniqueness — these are mathematical theorems that
   say something meaningful independent of implementation.

3. **CAS bugs exist.** SageMath, Mathematica, and Maple have all had
   bugs in polynomial factoring. A verified implementation provides
   independent confirmation.

4. **Bridge to formal mathematics.** The Mathlib bridge libraries give
   `Decidable` instances for `Irreducible`, enabling computation inside
   formal proofs. This unlocks constructive algebra in Lean: instead of
   "there exists an irreducible polynomial" you get "here is one, and
   here is a proof."

## Conformance testing

Every computational library is tested against SageMath:

1. Generate random polynomials in SageMath
2. Compute GCD/factorization/LLL reduction in SageMath
3. Run the same computation in Lean
4. Compare results

For LLL, also compare against `fpLLL` (the reference C implementation).

For polynomial factoring, generate certificates in SageMath and validate
in Lean (the certificate checker is the primary deliverable before full
algorithm verification).
