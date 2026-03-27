# lean-algebra — Verified Computational Algebra in Lean 4

A collection of cooperating Lean 4 libraries providing performant, verified
algorithms for computational algebra: polynomial arithmetic, factoring,
irreducibility testing, lattice basis reduction, and related tools.

## Design principles

1. **Many small libraries**, each its own Lake package in its own repo.

2. **No Mathlib in the computational core.** Every library that computes
   something is Mathlib-free. Separate `-verification` libraries depend on
   both the computational library and Mathlib to prove correspondence with
   Mathlib's mathematical definitions.

3. **Performant by default.** Dense array-backed representations, `UInt64`
   coefficients for `F_p`, Barrett/Montgomery reduction for modular
   arithmetic. FFI to FLINT as an optional fast path where it matters.
   New GMP `@[extern]` primitives where Lean's runtime doesn't yet expose
   what we need (modular exponentiation, extended GCD, etc.).

4. **Swappable polynomial representations.** A `PolyOps` typeclass lets
   algorithms work over any representation (dense, sparse sorted, sparse
   `ExtHashMap`-backed). A `LawfulPolyOps` class states the axioms. But
   the default — and the one everything is tested and proved against
   first — is dense `Array`-backed.

5. **Lean algorithms from the start.** All algorithms are implemented and
   run in Lean natively. No external CAS in the loop. Certificate
   structures exist for compact proof witnesses, but the algorithms that
   generate and check certificates are both in Lean.

6. **Clear DAG structure.** Libraries can be developed in parallel. LLL has
   no dependency on polynomial arithmetic. Hensel lifting is independent of
   LLL. Everything meets at the top (Berlekamp-Zassenhaus).

---

## Lean 4 stdlib inventory (v4.28.0)

What we get for free and what we need to build.

**Available:**
- `Nat.gcd` / `Int.gcd` — GMP-backed via `@[extern "lean_nat_gcd"]`
- `Nat.Coprime` — `gcd m n = 1`, decidable, with lemmas
- `Nat.lcm` / `Int.lcm`
- `Rat` — proper rational field with `Lean.Grind.Field` instance
- `Vector α n` — `Array α` with size proof, rich API (~19 files)
- `Fin n` — modular arithmetic with `Lean.Grind.CommRing` and `IsCharP`
- `BitVec w` — `Fin (2^w)`, extensive API, `bv_decide` support
- `Std.HashMap` / `Std.ExtHashMap` — the latter has extensionality
- `Lean.Grind.{Semiring, Ring, CommSemiring, CommRing, Field}` hierarchy

**Not available (we build):**
- Extended GCD / Bezout coefficients — completely absent
- Modular exponentiation — absent, and GMP's `mpz_powm` not exposed
- Modular inverse — absent, `mpz_invert` not exposed
- Primality testing — absent, `mpz_probab_prime_p` not exposed
- Polynomial types — none (only internal `grind` polynomials)
- Matrix types — none
- Finite field types / `ZMod` — absent (only `Fin n`)

**GMP primitives to expose (via `@[extern]` FFI, ideally upstreamed):**
- `mpz_powm` — modular exponentiation
- `mpz_gcdext` — extended GCD with Bezout coefficients
- `mpz_invert` — modular inverse
- `mpz_probab_prime_p` — probabilistic primality testing

These would live in `lean-gmp-extras` or be proposed as upstream additions
to the Lean runtime.

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
       lean-poly-fp     lean-poly-z    lean-matrix
       (poly over F_p)  (poly over Z)  (Vector of Vectors)
            |                |              |
            +-------+--------+              |
                    |                       |
               lean-poly                    |
               (poly interface +            |
                dense repr)                 |
                    |                       |
               lean-mod-arith               |
               (modular arithmetic)         |
                    |                       |
                    +----------+------------+
                               |
                          lean-arith
                          (extended GCD, Barrett,
                           GMP extras)

  Additional libraries (independent branches):

       lean-conway           lean-gfq-ring       lean-gfq-field
       (Conway polynomial    (GF(q) as a ring,   (GF(q) as a field,
        database)             quotient by any      requires
                              polynomial)          irreducibility)
            |                     |                    |
       lean-poly-fp          lean-poly-fp         lean-berlekamp
                                                  + lean-gfq-ring
```

**Verification libraries** (depend on computational lib + Mathlib):

```
    lean-berlekamp-zassenhaus-verification
    lean-berlekamp-verification
    lean-hensel-verification
    lean-lll-verification
    lean-poly-verification     (proves DensePoly R ≅ Polynomial R,
                                LawfulPolyOps gives ≃+*)
    lean-mod-arith-verification (proves ZMod64 p ≅ ZMod p)
    lean-gfq-verification     (proves GFq p n ≅ GaloisField p n)
```

Each verification library proves that the computational library's
operations correspond to Mathlib-defined mathematical objects.

---

## Library descriptions

### lean-arith (foundation, no dependencies)

Core integer arithmetic that everything else builds on.

**Contents:**
- Extended GCD for `Nat`, `Int`, and `UInt64`
- Barrett reduction for modular multiplication (precomputed inverse)
- Montgomery multiplication (for sustained modular arithmetic)
- Modular exponentiation by squaring
- Mignotte bound computation (coefficient bounds for polynomial factors)
- Cauchy root bound
- GMP FFI extras: `@[extern]` wrappers for `mpz_powm`, `mpz_gcdext`,
  `mpz_invert`, `mpz_probab_prime_p`
- Pure Lean implementations of the same for the proof target

**Key properties:**
- `extGcd a b = (g, s, t) → s * a + t * b = g ∧ g = gcd a b`
- `barrettMul a b p pinv = (a * b) % p`
- `powMod a n p = a ^ n % p`
- GMP FFI agrees with pure Lean implementation

**Note:** `Nat.gcd` already exists with GMP-backed `mpz_gcd`. We build on
it for extended GCD. The pure Lean `extGcd` is the proof target; the GMP
`mpz_gcdext` is the fast path with an equivalence proof.

---

### lean-matrix (foundation, depends on lean-arith)

Dense matrices as `Vector (Vector R m) n`.

**Contents:**
- `Matrix R n m` := `Vector (Vector R m) n` (uses stdlib `Vector`)
- Matrix-vector multiplication, matrix-matrix multiplication
- Dot product, norm squared (for `R = Int` and `R = Rat`)
- Determinant (Leibniz formula or Bareiss for integer matrices)
- Row operations (swap, scale, add multiple of one row to another)
- Row echelon form, rank, nullspace
- Generic over the coefficient type `R`

**Key properties:**
- Row operations preserve determinant (up to sign)
- `det (rowSwap M i j) = -det M`
- Nullspace correctness: `∀ v ∈ nullspace M, M * v = 0`

---

### lean-mod-arith (modular arithmetic, depends on lean-arith)

Arithmetic in `Z/nZ` with `UInt64`-backed coefficients.

**Contents:**
- `ZMod64 (p : Nat)` — a `UInt64` with proof `val.toNat < p`
- Addition, subtraction, multiplication with Barrett/Montgomery reduction
- Inversion via extended GCD (for prime moduli)
- Exponentiation by squaring
- `Lean.Grind.CommRing (ZMod64 p)` instance and `IsCharP (ZMod64 p) p`

**Key properties:**
- Ring axioms proved directly from the modular arithmetic definitions
- `inv a * a = 1` when `Nat.Coprime a.val p`
- Fermat's little theorem: `pow a (p-1) = 1` when `p` is prime and
  `a ≠ 0` — proved from the ring structure (the multiplicative group
  of a finite integral domain has order `p-1`)

**Note:** `Fin n` already has `Lean.Grind.CommRing` and `IsCharP`. We
build `ZMod64` for performance (Barrett reduction instead of naive modular
arithmetic) and for cleaner API (explicit prime parameter, field operations).

---

### lean-mod-arith-verification (depends on lean-mod-arith + Mathlib)

Proves `ZMod64 p ≃+* ZMod p`. This means any Mathlib theorem about
`ZMod p` transfers to `ZMod64 p`, and any computation with `ZMod64 p`
is known correct in the mathematical sense.

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

class LawfulPolyOps (P : Type*) (R : outParam Type*) [PolyOps P R] where
  add_comm : ∀ a b : P, add a b = add b a
  add_assoc : ∀ a b c : P, add (add a b) c = add a (add b c)
  mul_comm : ∀ a b : P, mul a b = mul b a
  mul_assoc : ∀ a b c : P, mul (mul a b) c = mul a (mul b c)
  add_zero : ∀ a : P, add a zero = a
  mul_one : ∀ a : P, mul a one = a
  left_distrib : ∀ a b c : P, mul a (add b c) = add (mul a b) (mul a c)
  coeff_add : ∀ (a b : P) (i : Nat), coeff (add a b) i = coeff a i + coeff b i
  coeff_mul : ∀ (a b : P) (i : Nat), coeff (mul a b) i = ...  -- convolution
  degree_add : ...
  degree_mul : ...
  divMod_spec : ∀ a b : P, let (q, r) := divMod a b; add (mul q b) r = a
  eval_C : ∀ r x, eval (C r) x = r
  eval_X : ∀ x, eval X x = x
  eval_add : ∀ p q x, eval (add p q) x = eval p x + eval q x
  eval_mul : ∀ p q x, eval (mul p q) x = eval p x * eval q x
  ext : ∀ p q : P, (∀ i, coeff p i = coeff q i) → p = q
```

**Dense representation:**
```lean
structure DensePoly (R : Type*) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ 0
```

The normalization invariant (no trailing zeros) ensures structural equality
= semantic equality. Every operation maintains this invariant.

**Operations:**
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

**Alternative representations (Phase 2):**

Sparse sorted array:
```lean
structure SparsePoly (R : Type*) [Zero R] [DecidableEq R] where
  terms : Array (Nat × R)
  sorted : ∀ i j, i < j → i < terms.size → j < terms.size →
           (terms[i]).1 < (terms[j]).1
  nonzero : ∀ i, i < terms.size → (terms[i]).2 ≠ 0
```

Sparse `ExtHashMap`-backed (with extensional equality):
```lean
structure ExtHashPoly (R : Type*) [Zero R] [BEq R] [Hashable Nat]
    [EquivBEq Nat] [LawfulHashable Nat] where
  map : ExtHashMap Nat R
  nonzero : ∀ k v, map.find? k = some v → v ≠ 0
```

Using `ExtHashMap` (not `HashMap`) gives extensionality lemmas — two
`ExtHashPoly` values are equal iff they have the same key-value pairs.

**Zero-value wrapper pattern:** For intermediate computation, use a raw
representation allowing zeros (no normalization overhead). Normalize on
output. This gives fast internals with clean equality on results.

---

### lean-poly-verification (depends on lean-poly + Mathlib)

Proves `DensePoly R ≃+* Polynomial R` and that `DensePoly` satisfies
`LawfulPolyOps`. The `≃+*` is the payoff of `LawfulPolyOps`:

```lean
def equiv [CommRing R] [DecidableEq R] : DensePoly R ≃+* Polynomial R

-- LawfulPolyOps gives ring equivalence
instance [CommRing R] [DecidableEq R] : LawfulPolyOps (DensePoly R) R := ...
```

Also proves GCD/ExtGCD correspondence with Mathlib's `Polynomial.gcd`.

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
- Square-free decomposition: output factors are pairwise coprime, their
  product equals the input, each factor is square-free

For `GF(2)` specifically, consider a packed bitwise representation:
```lean
structure GF2Poly where
  words : Array UInt64
  degree : Nat
```
Addition = XOR, multiplication uses carry-less multiply. 64x speedup
for `F_2` polynomials, important for coding theory.

---

### lean-poly-z (polynomials over Z, depends on lean-poly)

Specialized polynomial arithmetic over `Z`.

**Contents:**
- `ZPoly` = `DensePoly Int`
- Content and primitive part: `f = content(f) * primitivePart(f)`
- Gauss's lemma: the product of primitive polynomials is primitive
- Mignotte bound: coefficient bound for factors of `f`
- Reduction modulo p: `ZPoly → FpPoly p`

**Key properties:**
- `content(f * g) = content(f) * content(g)` (Gauss)
- `primitivePart(f)` is primitive (content = 1)
- Mignotte bound is valid: any factor of `f` has coefficients bounded by
  the computed bound

---

### lean-berlekamp (factoring over F_p, depends on lean-poly-fp + lean-matrix)

Berlekamp's algorithm and Rabin's irreducibility test for polynomials
over finite fields.

**Contents:**
- **Berlekamp matrix**: compute `Q_f`, the matrix of the Frobenius map
  `h ↦ h^p mod f` in the basis `{1, x, ..., x^{n-1}}`
- **Berlekamp kernel**: nullspace of `Q_f - I` (from lean-matrix)
- **Irreducibility test**: `f` is irreducible iff `rank(Q_f - I) = n - 1`
- **Factoring**: elements of the kernel split `f` via `gcd(f, h - c)`
- **Rabin's test**: `f` is irreducible iff `f | X^(p^n) - X` and
  `gcd(f, X^(p^(n/d)) - X) = 1` for each maximal proper divisor `d | n`
- **Distinct-degree factorization**: separate factors by degree

**Certificate structures** (generated and checked in Lean):
```lean
structure IrreducibilityCertificate (p n : Nat) where
  -- Square-and-multiply witnesses for X^(p^k) mod f
  powChain : Array (FpPoly p)
  -- Bezout coefficients for coprimality at each maximal divisor
  bezout : Array (FpPoly p × FpPoly p)
```

The certificate checker is tiny and fully verified. The algorithm that
*generates* certificates is also in Lean — Berlekamp's algorithm produces
the factorization, from which certificates are extracted.

**Key properties (characterizing):**

Rabin's theorem:
```lean
theorem rabin_irreducible (f : FpPoly p) (hf : f.degree = n) :
    rabinTest f = true ↔ Irreducible f
```

Berlekamp's theorem:
```lean
theorem berlekamp_complete (f : FpPoly p) (hf : squareFree f) :
    (berlekampFactor f).prod = f ∧
    ∀ g ∈ berlekampFactor f, Irreducible g
```

---

### lean-berlekamp-verification (depends on lean-berlekamp + Mathlib)

Connects the computational `Irreducible` to Mathlib's `Irreducible`
in `Polynomial (ZMod p)`. The payoff: a `Decidable` instance for
`Irreducible` on `Polynomial (ZMod p)`, backed by a verified algorithm.

```lean
instance [Fact (Nat.Prime p)] : DecidablePred (Irreducible · : Polynomial (ZMod p) → Prop)
```

---

### lean-conway (Conway polynomial database, depends on lean-poly-fp)

A database of Conway polynomials — canonical irreducible polynomials
`C(p, n)` for each prime `p` and degree `n`, satisfying compatibility
conditions across degree divisors.

**Contents:**
- Hardcoded database of Conway polynomials for commonly used `(p, n)` pairs
  (sourced from Frank Lübeck's tables)
- Lookup: `conwayPoly (p n : Nat) : Option (FpPoly p)`
- On-demand computation via Berlekamp for pairs not in the database
- Conway compatibility condition: if `m | n`, then `C(p, n) mod C(p, m)`
  generates `GF(p^m)` as a subfield of `GF(p^n)`

**Key properties:**
- Each `conwayPoly p n` is irreducible (checked against lean-berlekamp)
- Conway compatibility: divisor relationships are satisfied

---

### lean-gfq-ring (GF(q) as a ring, depends on lean-poly-fp)

Quotient ring `F_p[x] / (f)` for an arbitrary polynomial `f` over `F_p`.

**Contents:**
- `PolyQuotient p f` — elements of `F_p[x] / (f)`, represented as
  polynomials of degree < deg(f)
- Ring operations: addition, multiplication (multiply then reduce mod f),
  negation
- `Lean.Grind.CommRing` instance

This does NOT require `f` to be irreducible — the quotient is always a
ring. When `f` is irreducible, the quotient is a field, but that's
lean-gfq-field's job.

**Key properties:**
- Ring axioms
- `reduce (a * b) = reduce a * reduce b` (well-definedness of quotient)
- Canonical representative: degree < deg(f)

---

### lean-gfq-field (GF(q) as a field, depends on lean-gfq-ring + lean-berlekamp)

Extends `lean-gfq-ring` with field operations when the modulus is
irreducible.

**Contents:**
- `GFq p n` — the field `GF(p^n)`, constructed as
  `PolyQuotient p (conwayPoly p n)` with an irreducibility proof
- Multiplicative inverse via extended GCD in `F_p[x]`
- `Lean.Grind.Field` instance (when irreducibility is proved)
- Field with `p^n` elements, characteristic `p`
- `IsCharP (GFq p n) p`

The irreducibility proof comes from lean-berlekamp (either via the
algorithm or via a certificate for the Conway polynomial).

**Key properties:**
- `inv a * a = 1` for `a ≠ 0`
- `Fintype (GFq p n)` with `card = p^n`
- Frobenius automorphism: `frob(a) = a^p`

---

### lean-gfq-verification (depends on lean-gfq-field + Mathlib)

Proves `GFq p n ≃+* GaloisField p n` (Mathlib's Galois field).

---

### lean-hensel (Hensel lifting, depends on lean-poly-fp + lean-poly-z)

Lifts a factorization of `f mod p` to a factorization of `f mod p^k`.

**Contents:**
- **Linear Hensel lifting**: from `mod p^k` to `mod p^(k+1)`
- **Quadratic Hensel lifting**: from `mod p^k` to `mod p^(2k)` (doubling)
- **Multifactor lifting**: binary factor tree approach
- **Mignotte bound**: compute the required lifting height `k`

**Key properties:**
```lean
theorem hensel_correct (f g h : ZPoly) (p k : Nat) :
    let (g', h') := henselLift f g h p k
    g' * h' ≡ f [MOD p^(k+1)]

theorem hensel_extends (f g h : ZPoly) (p k : Nat) :
    let (g', h') := henselLift f g h p k
    g' ≡ g [MOD p^k] ∧ h' ≡ h [MOD p^k]

theorem hensel_degree (f g h : ZPoly) (p k : Nat) :
    let (g', h') := henselLift f g h p k
    g'.degree = g.degree ∧ h'.degree = h.degree

-- The deep theorem
theorem hensel_unique (f g h g' h' : ZPoly) (p k : Nat) :
    g.leadingCoeff = 1 →
    g * h ≡ f [MOD p^k] → g' * h' ≡ f [MOD p^k] →
    g ≡ g' [MOD p] → h ≡ h' [MOD p] →
    coprime_mod g h p →
    g = g' ∧ h = h'
```

**Strategy**: Start with linear lifting (simpler invariant, easier to
verify). Add quadratic as an optimization proved equivalent via uniqueness.

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
- D is a positive integer (integer lattice)
- Each swap decreases D by factor ≥ δ; size reduction doesn't change D
- At most `n(n-1)/2 · log(B) / log(1/δ)` swaps (polynomial bound)

**d-representation** (the Isabelle approach, avoids rationals):
Store `d_{i+1} · μ_{i,j}` where `d_i = det(Gram matrix of first i vectors)`.
All positive integers. No GCD, no fraction normalization.

**Key properties (all characterizing):**
```lean
theorem lll_same_lattice (b : Basis) (δ : Rat) :
    lattice (lll b δ) = lattice b

theorem lll_reduced (b : Basis) (δ : Rat) :
    isLLLReduced (lll b δ) δ

theorem lll_short_vector (b : Basis) (δ : Rat) (v : LatVector) :
    v ∈ lattice b → v ≠ 0 →
    ‖(lll b δ).head‖² ≤ α^(n-1) * ‖v‖²
  where α := 1 / (δ - 1/4)

theorem lll_swap_bound (b : Basis) (δ : Rat) :
    swapCount (lll b δ) ≤ n * (n-1) / 2 * log₂(maxNormSq b) / log₂(1/δ)
```

The short vector guarantee with `δ = 3/4` gives `‖b₁‖ ≤ 2^{(n-1)/2} · λ₁`.

Uses stdlib `Rat` for the specification; d-representation `Int` for
computation.

---

### lean-lll-verification (depends on lean-lll + Mathlib)

Connects lean-lll to Mathlib's linear algebra:
- Lattice corresponds to a `Submodule ℤ`
- GSO corresponds to Mathlib's `gramSchmidt`
- Short vector bound holds with respect to Mathlib's `norm`

---

### lean-berlekamp-zassenhaus (the capstone)

Depends on lean-berlekamp + lean-hensel + lean-lll.

Complete polynomial-time factoring of univariate polynomials over Z.

**Pipeline:**
1. `f` → `squareFreePart(f)` (Yun's algorithm, from lean-poly-z)
2. Choose prime `p` not dividing `disc(f)`, with `f mod p` square-free
3. `f mod p` → irreducible factors `g₁, ..., gᵣ mod p` (lean-berlekamp)
4. Hensel lift to `mod p^k` for Mignotte-bounded `k` (lean-hensel)
5. Recombine subsets of lifted factors to find true `Z[x]` factors
6. Step 5 uses LLL for polynomial-time recombination (lean-lll)

**Without LLL** (Phase 1): exponential-time subset recombination. Still
correct, just slow for high-degree polynomials with many factors mod p.

**With LLL** (Phase 2): polynomial-time recombination. Short lattice
vectors correspond to true factors.

**Key properties:**
```lean
theorem factor_product (f : ZPoly) :
    (factor f).prod = f

theorem factor_irreducible (f : ZPoly) :
    ∀ g ∈ factor f, Irreducible g

theorem factor_unique (f : ZPoly) (gs hs : List ZPoly) :
    gs.prod = f → hs.prod = f →
    (∀ g ∈ gs, Irreducible g) → (∀ h ∈ hs, Irreducible h) →
    gs ~ hs  -- multiset equality up to associates
```

**Certificate structures for Z[x] irreducibility:**
```lean
structure ZPolyIrreducibilityCertificate where
  primes : Array Nat
  factorDegrees : Array (Array Nat)
  factorCerts : Array (Array IrreducibilityCertificate)
  -- Degree analysis: intersection of subset sums = {0, deg(f)}

structure LPFWCertificate where
  evalPoint : Int
  prime : Nat
  quotient : Nat
  cauchyBound : Rat
  degreeBound : Nat
  -- Verification: P is prime, f(m) = ±quotient * P, quotient < (|m| - ρ)^d
```

---

## Dependency DAG (for parallel development)

```
Phase 0 (all parallel, no dependencies between them):
  ├── lean-arith
  └── (lean-poly can start with inline arith)

Phase 1 (each depends only on Phase 0):
  ├── lean-mod-arith          (← lean-arith)
  ├── lean-poly               (← lean-arith)
  ├── lean-matrix             (← lean-arith)
  └── lean-lll                (← lean-matrix)

Phase 2 (each depends on Phase 1):
  ├── lean-poly-fp            (← lean-poly + lean-mod-arith)
  ├── lean-poly-z             (← lean-poly)
  └── lean-lll is complete    (independent)

Phase 3 (each depends on Phase 2):
  ├── lean-berlekamp          (← lean-poly-fp + lean-matrix)
  ├── lean-hensel             (← lean-poly-fp + lean-poly-z)
  ├── lean-conway             (← lean-poly-fp)
  └── lean-gfq-ring           (← lean-poly-fp)

Phase 4:
  ├── lean-gfq-field          (← lean-gfq-ring + lean-berlekamp)
  └── lean-berlekamp-zassenhaus (← lean-berlekamp + lean-hensel + lean-lll)

Verification libraries (can start whenever their core lib is ready):
  ├── lean-mod-arith-verification  (Phase 1+)
  ├── lean-poly-verification       (Phase 1+)
  ├── lean-berlekamp-verification  (Phase 3+)
  ├── lean-hensel-verification     (Phase 3+)
  ├── lean-lll-verification        (Phase 1+)
  └── lean-gfq-verification       (Phase 4+)
```

**Key insight:** LLL is completely independent of the polynomial pipeline.
It can be developed from day one in parallel with everything else. The
only point of contact is at the very top (Berlekamp-Zassenhaus).

---

## Milestones

**M1:** lean-arith + lean-poly + lean-mod-arith working. Polynomial
arithmetic over Z and F_p. GCD, extended GCD, division. Conformance-
tested against FLINT via FFI.

**M2 (parallel with M1):** lean-matrix + lean-lll working. LLL reduces
lattice bases with verified short vector guarantee.

**M3 (after M1):** lean-berlekamp working. Factor polynomials over F_p,
test irreducibility. Certificate generation and checking, all in Lean.

**M4 (after M1):** lean-hensel working. Lift factorizations from F_p
to Z/p^kZ.

**M5 (after M3):** lean-conway + lean-gfq-ring + lean-gfq-field working.
Finite field arithmetic with verified field structure.

**M6 (after M2+M3+M4):** lean-berlekamp-zassenhaus. Complete verified
polynomial factoring over Z.

**M7 (ongoing):** Verification libraries connecting to Mathlib.
`Decidable` instance for `Irreducible` on `Polynomial (ZMod p)`.

---

## Polynomial representation design

### Primary: Dense (Array-backed)

```lean
structure DensePoly (R : Type*) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ 0
```

- Index = degree, `coeffs[i]` is coefficient of `x^i`
- Normalization invariant: no trailing zeros
- Structural equality = semantic equality
- O(1) degree, O(1) coefficient access

### Secondary: Sparse sorted (Array of pairs)

```lean
structure SparsePoly (R : Type*) [Zero R] [DecidableEq R] where
  terms : Array (Nat × R)
  sorted : ∀ i j, i < j → i < terms.size → j < terms.size →
           (terms[i]).1 < (terms[j]).1
  nonzero : ∀ i, i < terms.size → (terms[i]).2 ≠ 0
```

### Tertiary: Sparse ExtHashMap-backed

```lean
structure ExtHashPoly (R : Type*) [Zero R] [BEq R] [Hashable Nat]
    [EquivBEq Nat] [LawfulHashable Nat] where
  map : ExtHashMap Nat R
  nonzero : ∀ k v, map.find? k = some v → v ≠ 0
```

`ExtHashMap` provides extensionality: two maps are equal iff they have the
same key-value pairs. No iteration order issues.

### The typeclasses

`PolyOps` for operations, `LawfulPolyOps` for axioms. Algorithms are
written against `PolyOps`. In the verification library, `LawfulPolyOps`
gives the ring equivalence `P ≃+* Polynomial R`.

### Zero-value wrapper pattern

For intermediate computation, use raw representation allowing zeros (no
normalization overhead). Normalize on output for clean equality.

---

## Practical applications

**Cryptographic field construction:** To build `GF(2^128)` for AES, you
need an irreducible polynomial of degree 128 over `F_2`. With
lean-berlekamp, produce a Lean proof that it's irreducible.

**Coding theory:** Reed-Solomon and BCH codes need irreducible polynomials
over finite fields. Verified factoring provides certified generator
polynomials.

**Number theory:** Computing rings of integers requires factoring
polynomials over Z. The Baanen et al. project currently delegates to
SageMath with unverified certificates — this replaces that dependency.

**Cryptanalysis:** LLL is the core tool for lattice-based attacks. A
verified LLL gives confidence in attack results.

---

## Prior art

**Isabelle/HOL** (the gold standard): The Innsbruck group verified the
entire Berlekamp-Zassenhaus + LLL pipeline. Degree-500 polynomials factor
at 2.5x Mathematica speed. ~44K lines across multiple AFP entries.

**Baanen et al. (Lean 4)**: Certificate-based irreducibility checking for
the rings-of-integers project. Uses `decide`/`native_decide` on list-based
polynomials. Works but doesn't scale beyond small degrees.

**CoqEAL (Coq)**: Verified Karatsuba, Strassen, Bareiss, Smith normal form.
Refinement-based approach.

**FLINT (C)**: The performance target. Dense `nmod_poly` and `fmpz_poly`
with Barrett reduction, Karatsuba, NTT. Not verified.

---

## What verification buys you

1. **Results depend on algorithms being correct.** CAS systems have bugs
   in polynomial factoring. A verified implementation provides independent
   confirmation that a polynomial is (or isn't) irreducible.

2. **The properties are characterizing.** Rabin's theorem, the Lovász
   condition, Hensel uniqueness — mathematical theorems that say something
   meaningful independent of implementation.

3. **Bridge to formal mathematics.** The verification libraries give
   `Decidable` instances for `Irreducible`, enabling computation inside
   formal proofs. Instead of "there exists an irreducible polynomial" you
   get "here is one, and here is a proof."

## Repository structure

Separate repos per library, with each repo containing a single Lake
package. This gives clean dependency management and allows independent
versioning. The cost is cross-repo development friction, but:

- Lake handles git dependencies natively
- Each library is small enough to stabilize independently
- Verification libraries can track Mathlib's toolchain independently
  of the computational libraries
- Contributors can work on lean-lll without pulling lean-poly

For the initial bootstrapping phase, a single monorepo with multiple
Lake packages is acceptable, splitting into separate repos once the
APIs stabilize.

## Conformance testing

Every computational library is tested against FLINT via C FFI:

1. Generate random polynomials
2. Compute GCD/factorization/LLL reduction in both Lean and FLINT
3. Compare results

For LLL, also compare against `fpLLL` (the reference C implementation).

For polynomial factoring, generate certificates in Lean (via
lean-berlekamp), validate them, and cross-check the factorization
against FLINT.
