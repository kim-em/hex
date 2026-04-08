# hex — Verified Computational Algebra in Lean 4

A collection of cooperating Lean 4 libraries providing performant, verified
algorithms for computational algebra: polynomial arithmetic, factoring,
irreducibility testing, finite field construction, lattice basis reduction,
and related tools.

## Design principles

1. **Many small libraries**, each its own Lake package in its own repo.

2. **No Mathlib in the computational core.** Every library that computes
   something is Mathlib-free. Where full correctness requires results
   from analysis (e.g. the Mignotte bound), the computational
   library proves conditional correctness and the corresponding
   `-mathlib` library discharges the hypothesis. The `-mathlib`
   libraries also prove correspondence with Mathlib's mathematical
   definitions (e.g. `ZMod64 p ≃+* ZMod p`).

3. **Performant by default.** Dense array-backed representations, `UInt64`
   coefficients for `F_p`, Barrett/Montgomery reduction for modular
   arithmetic. New GMP `@[extern]` primitives where Lean's runtime
   doesn't yet expose what we need (modular exponentiation, extended
   GCD, etc.). FLINT is used for conformance testing, not as a runtime
   dependency.

4. **Swappable polynomial representations.** A `PolyOps` typeclass defines
   operations including `dropZeros : P → P` (normalize to canonical form).
   `LawfulPolyOps` states the ring axioms and that `dropZeros` is
   idempotent, preserves coefficients, and gives extensionality on the
   subtype `{ p : P // dropZeros p = p }`. The default representation is
   dense `Array`-backed. Subtypes throughout, never quotients.

5. **Lean algorithms from the start.** All algorithms are implemented and
   run in Lean natively. No external CAS in the loop. Certificate
   structures exist for compact proof witnesses, but the algorithms that
   generate and check certificates are both in Lean.

6. **Clear DAG structure.** Libraries can be developed in parallel. LLL has
   no dependency on polynomial arithmetic. Hensel lifting is independent of
   LLL. Everything meets at the top (Berlekamp-Zassenhaus).

7. **`ComputationalAlgebra` namespace.** All definitions live under
   `ComputationalAlgebra` to avoid collisions with Mathlib's root-namespace
   types (`Matrix`, `Polynomial`, etc.).

---

## Lean 4 stdlib inventory (v4.28.0)

What we get for free and what we need to build.

**Available:**
- `Nat.gcd` / `Int.gcd` — GMP-backed via `@[extern "lean_nat_gcd"]`
- `Nat.divExact` / `Int.divExact` — GMP-backed (`mpz_divexact`), requires
  divisibility proof; faster than regular division
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
- Primality testing — absent (not needed for this project; Berlekamp-
  Zassenhaus only needs small known primes)
- Polynomial types — none (only internal `grind` polynomials)
- Matrix types — none
- Finite field types / `ZMod` — absent (only `Fin n`)

**GMP primitives to expose (via `@[extern]` FFI, ideally upstreamed):**
- `mpz_powm` — modular exponentiation
- `mpz_gcdext` — extended GCD with Bezout coefficients
- `mpz_invert` — modular inverse

These would live in `hex-gmp-extras` or be proposed as upstream additions
to the Lean runtime.

---

## Libraries

- **hex-arith** — extended GCD, Barrett/Montgomery reduction, binomial coefficients, Fermat's little theorem
- **hex-poly** — polynomial typeclass interface + dense `Array`-backed representation
- **hex-matrix** — dense matrices as `Vector (Vector R m) n`, RREF, Bareiss determinant, span, nullspace
- **hex-gram-schmidt** — Gram-Schmidt orthogonalization, GS coefficients, Gram determinants, update formulas under row operations
- **hex-mod-arith** — `ZMod64 p`: `UInt64`-backed arithmetic in `Z/pZ`
- **hex-poly-fp** — polynomials over `F_p`, Frobenius map, square-free decomposition
- **hex-poly-z** — polynomials over `Z`, content/primitive part, Mignotte bound
- **hex-berlekamp** — Berlekamp factoring and Rabin irreducibility test over `F_p`
- **hex-hensel** — Hensel lifting from `mod p` to `mod p^k`
- **hex-lll** — LLL lattice basis reduction
- **hex-berlekamp-zassenhaus** — complete factoring of `Z[x]`
- **hex-conway** — Conway polynomial database
- **hex-gfq-ring** — quotient ring `F_p[x]/(f)`
- **hex-gfq-field** — field structure when `f` is irreducible
- **hex-gfq** — convenience wrapper: `GFq p n` using Conway polynomials

## Library DAG

Three independent roots: hex-poly, hex-arith, hex-matrix.

```
      hex-poly     hex-arith      hex-matrix
       /     \          |            /       \
      /       \     hex-mod-arith  /  hex-gram-schmidt
     /         \       /           /         |
hex-poly-z  hex-poly-fp         /       hex-lll
     \        /       |          /         /
     hex-hensel  hex-gfq-ring /         /
               \       |       /         /
                \  hex-berlekamp       /
                 \      |              /
                  hex-berlekamp-zassenhaus
```

Additional libraries (finite field construction):
```
        hex-berlekamp
         /          \
  hex-gfq-field  hex-conway
         \          /
          hex-gfq
```

**Mathlib bridge libraries** (each depends on a computational lib + Mathlib,
proving correspondence with Mathlib's mathematical definitions):

- **hex-mod-arith-mathlib** — `ZMod64 p ≃+* ZMod p`
- **hex-poly-mathlib** — `DensePoly R ≃+* Polynomial R` via `LawfulPolyOps`
- **hex-matrix-mathlib** — matrix equivalence, `det` agreement, rank = `Matrix.rank`, nullspace = `LinearMap.ker`, row ops = transvections
- **hex-gram-schmidt-mathlib** — `GramSchmidt.Int.basis` = Mathlib's `gramSchmidt`
- **hex-poly-z-mathlib** — `DensePoly Int ≃+* Polynomial ℤ`, Mignotte bound (via Mathlib's Mahler measure)
- **hex-berlekamp-mathlib** — `Decidable (Irreducible f)` for `Polynomial (ZMod p)`
- **hex-hensel-mathlib** — Hensel lifting corresponds to Mathlib's `Polynomial` factoring
- **hex-lll-mathlib** — lattice = `Submodule ℤ`, short vector bound
- **hex-gfq-mathlib** — `GFq p n ≃+* GaloisField p n`
- **hex-berlekamp-zassenhaus-mathlib** — unconditional factoring correctness, `Decidable (Irreducible f)` for `Polynomial ℤ`

---

## Library descriptions

### hex-arith (no dependencies)

Core integer arithmetic that everything else builds on.

**Contents:**

- Extended GCD for `Nat`, `Int`, and `UInt64`
- Barrett and Montgomery reduction for `UInt64` modular arithmetic
  (see below)
- Modular exponentiation by squaring (using Montgomery internally)
- GMP FFI extras: `@[extern]` wrappers for `mpz_powm`, `mpz_gcdext`,
  `mpz_invert` — for big-integer operations where values exceed 64 bits
- Pure Lean implementations of the same for the proof target

**Barrett reduction** — fast single modular multiplication on `UInt64`.
Precompute an approximate reciprocal of the modulus, then reduce via
multiply + shift instead of division.

```lean
structure BarrettCtx (p : UInt64) where
  p_pos : p > 0
  pinv : UInt64
  pinv_eq : pinv = .ofNat (2 ^ 64 / p.toNat)

def BarrettCtx.mk (p : UInt64) (hp : p > 0) : BarrettCtx p
def BarrettCtx.mulMod (ctx : BarrettCtx p) (a b : UInt64) : UInt64
```

Key properties:
```lean
theorem BarrettCtx.mulMod_lt (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b < p

theorem BarrettCtx.toNat_mulMod (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat

theorem BarrettCtx.mulMod_eq (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b = .mk ⟨(a.toNat * b.toNat) % p.toNat, by omega⟩
```

**Montgomery reduction** — optimized for sustained modular arithmetic
(sequences of multiplications with the same modulus, e.g. exponentiation
by squaring, polynomial evaluation over F_p).

Values are stored in Montgomery form: `a` is represented as `a * R mod p`
where `R = 2^64`. Reduction uses the low bits of the product (a mask)
instead of division.

```lean
structure MontCtx (p : UInt64) where
  p_odd : p % 2 = 1
  p' : UInt64
  p'_eq : (p'.toNat * p.toNat) % 2 ^ 64 = 2 ^ 64 - 1
  r2 : UInt64
  r2_eq : r2.toNat = (2 ^ 64 * 2 ^ 64) % p.toNat

def MontCtx.mk (p : UInt64) (hp : p % 2 = 1) : MontCtx p
def MontCtx.toMont (ctx : MontCtx p) (a : UInt64) : UInt64
def MontCtx.fromMont (ctx : MontCtx p) (a : UInt64) : UInt64
def MontCtx.mulMont (ctx : MontCtx p) (a b : UInt64) : UInt64
```

Key properties:
```lean
theorem MontCtx.fromMont_toMont (ctx : MontCtx p) (a : UInt64)
    (ha : a < p) :
    ctx.fromMont (ctx.toMont a) = a

theorem MontCtx.toNat_mulMont (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat

theorem MontCtx.mulMont_eq (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b)) =
      .mk ⟨(a.toNat * b.toNat) % p.toNat, by omega⟩
```

**When to use which:** Barrett for one-off or few modular operations.
Montgomery for hot loops (exponentiation, Frobenius map, polynomial
multiplication over F_p) where the conversion overhead is amortized.

**Extended GCD:**
```lean
def extGcd (a b : Nat) : Nat × Int × Int

theorem extGcd_fst (a b : Nat) : (extGcd a b).1 = Nat.gcd a b

theorem extGcd_bezout (a b : Nat) :
    let (g, s, t) := extGcd a b
    s * a + t * b = g
```
Also for `Int` and `UInt64` variants.

**Modular exponentiation:**
```lean
def powMod (a n p : Nat) : Nat  -- uses Montgomery internally

theorem powMod_eq (a n p : Nat) (hp : p > 0) :
    powMod a n p = a ^ n % p
```

**Binomial coefficients and Fermat's little theorem:**

`Nat.choose` is in Mathlib, not Init, so we define it here
(standard recursive definition). We prove the key lemma and Fermat's
little theorem:
```lean
theorem Nat.choose_prime_dvd (hp : Nat.Prime p) (hk : 0 < k) (hk' : k < p) :
    p ∣ Nat.choose p k

theorem Nat.add_pow_prime_mod (hp : Nat.Prime p) (a b : Nat) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p

theorem Nat.pow_prime_mod (hp : Nat.Prime p) (a : Nat) :
    a ^ p % p = a % p
```
Proof: `choose_prime_dvd` by Euclid's lemma (since `k! * C(p,k)` has
factor `p` but `gcd(p, k!) = 1`). `add_pow_prime_mod` follows
(all middle binomial terms vanish mod p). `pow_prime_mod` by induction
on `a`: base `0^p = 0`, step uses `add_pow_prime_mod` with `b = 1`.

**Euclid's lemma:**
```lean
theorem Nat.Prime.dvd_mul (hp : Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b
```
Proof via extended GCD: if `p ∤ a` then `gcd(a, p) = 1`, Bezout gives
`s * a + t * p = 1`, multiply by `b`, since `p ∣ a * b` conclude `p ∣ b`.

**Note:** `Nat.gcd` already exists with GMP-backed `mpz_gcd`. We build on
it for extended GCD. The pure Lean `extGcd` is the logical definition used
in proofs; the GMP `@[extern]` for `mpz_gcdext` replaces it at runtime,
trusted in the same way as every other `@[extern]` in Lean.

---

### hex-matrix (foundation, no dependencies)

Dense matrices as `Vector (Vector R m) n`.

**Contents:**
- `Matrix R n m` := `Vector (Vector R m) n` (uses stdlib `Vector`)
- Matrix-vector multiplication, matrix-matrix multiplication
- Dot product, norm squared (for `R = Int` and `R = Rat`)
- Row operations (swap, scale, add multiple of one row to another)
- Row reduction (RREF over fields) and span/nullspace machinery:

  ```lean
  /-- Pure data: the result of row-reducing a matrix. -/
  structure RowEchelonData (R : Type) (n m : Nat) where
    rank : Nat
    echelon : Matrix R n m
    transform : Matrix R n n
    pivotCols : Vector (Fin m) rank

  /-- Shared conditions for any echelon form (RREF or HNF). -/
  structure IsEchelonForm (M : Matrix R n m) (D : RowEchelonData R n m) : Prop where
    transform_mul : D.transform * M = D.echelon
    transform_inv : ∃ u, det D.transform * u = 1
    rank_le_n : D.rank ≤ n
    rank_le_m : D.rank ≤ m
    pivotCols_sorted : ∀ i j, i < j → D.pivotCols[i] < D.pivotCols[j]
    below_pivot_zero : ...  -- entries below each pivot are zero

  /-- RREF-specific: pivots are 1, everything above is 0. -/
  structure IsRREF (M : Matrix R n m) (D : RowEchelonData R n m)
      extends IsEchelonForm M D : Prop where
    pivot_one : ...         -- each pivot is 1
    above_pivot_zero : ...  -- entries above each pivot are 0

  def rref (M : Matrix R n m) : RowEchelonData R n m
  theorem rref_isRREF (M : Matrix R n m) : IsRREF M (rref M)
  ```

  **Span via echelon form.** Given an `IsEchelonForm`, solve for
  coefficients or test membership. Works for both RREF and HNF.

  ```lean
  def IsEchelonForm.spanCoeffs (F : IsEchelonForm M D)
      (v : Vector R m) : Option (Vector R n)
  def IsEchelonForm.spanContains (F : IsEchelonForm M D)
      (v : Vector R m) : Bool

  /-- Convenience: compute RREF internally. -/
  def Matrix.spanCoeffs (M : Matrix R n m) (v : Vector R m) :
      Option (Vector R n)
  def Matrix.spanContains (M : Matrix R n m) (v : Vector R m) : Bool
  ```

  **Nullspace** via echelon form. Each free variable gives one basis
  vector.

  ```lean
  def IsEchelonForm.nullspace (F : IsEchelonForm M D) :
      Array (Vector R m)

  /-- Convenience wrapper. -/
  def Matrix.nullspace (M : Matrix R n m) : Array (Vector R m)
  ```

- Generic over the coefficient type `R`

**Determinant — definition and computation:**

Define `det` via the Leibniz formula (sum over permutations), over any
`Ring`. (Theorems about `det` will require `CommRing`.)

For computation, provide the Bareiss algorithm (fraction-free Gaussian
elimination) over `Int`. The Bareiss recurrence at step k is:
```
a_{ij}^{(k)} = (a_{kk}^{(k-1)} · a_{ij}^{(k-1)} - a_{ik}^{(k-1)} · a_{kj}^{(k-1)}) / a_{k-1,k-1}^{(k-2)}
```
where `/` is `Int.divExact` (GMP-backed `mpz_divexact`) — the division is
always exact, and the divisibility proof is carried.

**Proof that `bareiss M = det M`:** Via row operations. Each Bareiss
step is equivalent to: scale rows below the pivot,
subtract the appropriate multiple, then divide out the accumulated extra
factor. The row operation lemmas (proved directly from Leibniz) track
`det` through each step, and the scaling factors telescope due to the
division by the previous pivot.

**Key properties:**
- `det_one : det 1 = 1`
- `det_rowSwap : i ≠ j → det (rowSwap M i j) = -det M`
- `det_rowScale : det (rowScale M i c) = c * det M`
- `det_rowAdd : i ≠ j → det (rowAdd M i j c) = det M`
- `bareiss_eq_det : bareiss M = det M`
- `spanCoeffs_sound : E.spanCoeffs v = some c → M * c = v`
- `spanCoeffs_complete : (∃ c, M * c = v) → (E.spanCoeffs v).isSome`
- `spanContains_iff : E.spanContains v = true ↔ ∃ c, M * c = v`
- Nullspace soundness: `∀ v ∈ E.nullspace, M * v = 0`
- Nullspace completeness: `M * v = 0 → E.nullspace.toMatrix.spanContains v`
- Rank-nullity: `E.nullspace.size + D.rank = m`

---

### hex-matrix-mathlib (depends on hex-matrix + Mathlib)

Proves that our matrix type and operations correspond to Mathlib's
abstract linear algebra.

Mathlib has no RREF, but does have `Matrix.transvection` (elementary
row operations), `TransvectionStruct`, and a `Pivot` namespace that
reduces matrices to diagonal form via transvections. Mathlib's rank,
kernel, and span are noncomputable (cardinals, infima over submodules).
This bridge connects our computable versions to those definitions.

**Matrix equivalence:**
```lean
def matrixEquiv :
    ComputationalAlgebra.Matrix R n m ≃ Matrix (Fin n) (Fin m) R
```

**Row operations correspond to Mathlib transvections:**
Our `rowAdd M i j c` is left-multiplication by
`Matrix.transvection i j c`. Our `rowSwap` and `rowScale` correspond
to Mathlib's `Equiv.swap` and diagonal matrices.

**Determinant:**
```lean
theorem det_eq (M : ComputationalAlgebra.Matrix R n n) :
    ComputationalAlgebra.det M = Matrix.det (matrixEquiv M)
```

**Rank:** Our `RowEchelonData.rank` (computed via RREF) agrees with
Mathlib's `Matrix.rank` (noncomputable, defined as
`finrank R (LinearMap.range M.mulVecLin)`).
```lean
theorem rank_eq (M : ComputationalAlgebra.Matrix R n m)
    (D : RowEchelonData R n m) (E : IsEchelonForm M D) :
    D.rank = Matrix.rank (matrixEquiv M)
```

**Nullspace:** Our computed nullspace basis spans the same submodule
as `LinearMap.ker (Matrix.mulVecLin (matrixEquiv M))`.

**Span:** Our `IsEchelonForm.spanContains` agrees with membership in
`Submodule.span R (Set.range M.row)`.

This means Mathlib theorems (Cramer's rule, Cayley-Hamilton,
rank-nullity, `diagonal_transvection_induction`) transfer to our
matrices, and our computations give computable witnesses for
Mathlib's noncomputable definitions.

---

### hex-mod-arith (modular arithmetic, depends on hex-arith)

Arithmetic in `Z/nZ` with `UInt64`-backed coefficients.

**Contents:**
- `ZMod64 (p : Nat)` — a `UInt64` with proof `val.toNat < p`
- Addition, subtraction, multiplication (using Barrett/Montgomery from
  hex-arith for the `UInt64` modular operations)
- Inversion via extended GCD (for prime moduli)
- Exponentiation by squaring
- `Lean.Grind.CommRing (ZMod64 p)` instance and `IsCharP (ZMod64 p) p`

**Key properties:**
- Ring axioms proved directly from the modular arithmetic definitions.
  Associativity and distributivity of multiplication reduce to
  `Nat.mod` properties via Barrett/Montgomery correctness from
  hex-arith.
- `inv a * a = 1` when `Nat.Coprime a.val p` — via extended GCD
  from hex-arith: `s * a + t * p = 1` gives `s mod p` as the inverse.
- No zero divisors for prime `p`: `a * b = 0 → a = 0 ∨ b = 0` — via
  Euclid's lemma from hex-arith.
- Fermat's little theorem: `a ^ p = a` — lifts directly from
  `Nat.pow_prime_mod` in hex-arith.

**Note:** `Fin n` already has `Lean.Grind.CommRing` and `IsCharP`. We
build `ZMod64` for performance (Barrett reduction instead of naive modular
arithmetic) and for cleaner API (explicit prime parameter, field operations).

---

### hex-mod-arith-mathlib (depends on hex-mod-arith + Mathlib)

Proves `ZMod64 p ≃+* ZMod p`. This means any Mathlib theorem about
`ZMod p` transfers to `ZMod64 p`, and any computation with `ZMod64 p`
is known correct in the mathematical sense.

---

### hex-poly (polynomial interface + dense representation, no dependencies)

The core polynomial library. Defines both the typeclass interface and the
default dense representation.

**Typeclass interface:**
```lean
class PolyOps (P : Type*) (R : outParam Type*) extends
    Add P, Mul P, Neg P, Zero P, One P, BEq P where
  X : P
  C : R → P
  degree : P → Nat
  coeff : P → Nat → R
  leadingCoeff : P → R
  dropZeros : P → P
  divMod : P → P → P × P
  eval : P → R → R
  ofCoeffs : Array R → P
  toCoeffs : P → Array R

class LawfulPolyOps (P : Type*) (R : outParam Type*) [PolyOps P R] where
  -- Ring axioms
  add_comm : ∀ a b : P, a + b = b + a
  add_assoc : ∀ a b c : P, a + b + c = a + (b + c)
  mul_comm : ∀ a b : P, a * b = b * a
  mul_assoc : ∀ a b c : P, a * b * c = a * (b * c)
  add_zero : ∀ a : P, a + 0 = a
  mul_one : ∀ a : P, a * 1 = a
  left_distrib : ∀ a b c : P, a * (b + c) = a * b + a * c
  -- Coefficient semantics
  coeff_add : ∀ (a b : P) (i : Nat), coeff (a + b) i = coeff a i + coeff b i
  coeff_mul : ...  -- convolution formula
  -- BEq correctness: == agrees with coefficient equality
  beq_iff : ∀ a b : P, (a == b) = true ↔ ∀ i, coeff a i = coeff b i
  -- dropZeros: normalization to canonical form
  dropZeros_idem : ∀ p, dropZeros (dropZeros p) = dropZeros p
  dropZeros_coeff : ∀ p i, coeff (dropZeros p) i = coeff p i
  dropZeros_ext : ∀ p q, dropZeros p = p → dropZeros q = q →
      (∀ i, coeff p i = coeff q i) → p = q
  -- Division
  divMod_spec : ∀ a b : P, let (q, r) := divMod a b; q * b + r = a
  -- Evaluation is a ring homomorphism
  eval_C : ∀ r x, eval (C r) x = r
  eval_X : ∀ x, eval X x = x
  eval_add : ∀ p q x, eval (p + q) x = eval p x + eval q x
  eval_mul : ∀ p q x, eval (p * q) x = eval p x * eval q x
```

**`dropZeros` is the canonical form function.** For dense representations,
it strips trailing zeros. For sparse representations, it removes entries
with zero coefficients. `dropZeros_ext` gives extensionality on the
subtype `{ p : P // dropZeros p = p }` — two canonical-form polynomials
with the same coefficients are propositionally equal.

**The subtype `CanonicalPoly P := { p : P // dropZeros p = p }`** is where
the `≃+*` lives. In the `-mathlib` bridge library:

```lean
def CanonicalPoly (P : Type*) [PolyOps P R] := { p : P // dropZeros p = p }

-- The -mathlib bridge library proves:
def equiv [LawfulPolyOps P R] : CanonicalPoly P ≃+* Polynomial R
```

Eagerly-normalizing implementations (like `DensePoly`) satisfy
`dropZeros = id`, so `CanonicalPoly (DensePoly R) ≃ DensePoly R` and
the subtype wrapper is trivial. Lazy implementations pay the cost of
normalization only when they need propositional equality.

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

**Existential CRT for polynomials** (corollary of Bezout):

```lean
def polyCRT [PolyOps P R] (a b u v s t : P) : P :=
  u * t * b + v * s * a

theorem polyCRT_mod_fst [LawfulPolyOps P R] (a b u v s t : P)
    (hbez : s * a + t * b = 1) :
    (polyCRT a b u v s t) % a = u % a

theorem polyCRT_mod_snd [LawfulPolyOps P R] (a b u v s t : P)
    (hbez : s * a + t * b = 1) :
    (polyCRT a b u v s t) % b = v % b
```

Given coprime `a, b` with Bezout coefficients `s, t`, constructs `h`
with `h ≡ u (mod a)` and `h ≡ v (mod b)`. Used by hex-hensel,
hex-gfq-ring, and hex-berlekamp-mathlib (Berlekamp correctness proof).

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

**Normalization:** `DensePoly` normalizes eagerly, so `dropZeros = id`
and `CanonicalPoly (DensePoly R) ≃ DensePoly R` trivially. Sparse
representations may defer normalization, paying the cost only when
propositional equality is needed (via `dropZeros`).

---

### hex-poly-mathlib (depends on hex-poly + Mathlib)

Proves `LawfulPolyOps` for `DensePoly R` and constructs the ring
equivalence. Since `DensePoly` normalizes eagerly, `dropZeros = id`
and `CanonicalPoly (DensePoly R)` is trivially `DensePoly R`:

```lean
instance [CommRing R] [DecidableEq R] : LawfulPolyOps (DensePoly R) R := ...

-- dropZeros is id for DensePoly, so CanonicalPoly is trivial
def equiv [CommRing R] [DecidableEq R] : DensePoly R ≃+* Polynomial R
```

Also proves GCD/ExtGCD correspondence with Mathlib's `Polynomial.gcd`.

---

### hex-poly-fp (polynomials over F_p, depends on hex-poly + hex-mod-arith)

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

### hex-poly-z (polynomials over Z, depends on hex-poly)

Specialized polynomial arithmetic over `Z`.

**Contents:**
- `ZPoly` = `DensePoly Int`
- Polynomial congruence:
  ```lean
  def ZPoly.congr (f g : ZPoly) (m : Nat) : Prop :=
      ∀ i, (f.coeff i - g.coeff i) % m = 0

  def ZPoly.coprimeModP (f g : ZPoly) (p : Nat) : Prop := ...
  ```
- Content and primitive part: `f = content(f) * primitivePart(f)`
- Gauss's lemma: the product of primitive polynomials is primitive
- Mignotte bound computation: `|gⱼ| ≤ C(k,j) · ‖f‖₂` for any degree-k
  factor `g | f` in `Z[x]`. The computation is just binomial coefficients
  and the 2-norm of `f`'s coefficients. The proof that the bound is valid
  lives in `hex-poly-z-mathlib`.
- Reduction modulo p: `ZPoly → FpPoly p`

**Key properties:**
- `content(f * g) = content(f) * content(g)` (Gauss)
- `primitivePart(f)` is primitive (content = 1)

---

### hex-poly-z-mathlib (depends on hex-poly-z + Mathlib)

Proves `DensePoly Int ≃+* Polynomial ℤ` and the Mignotte bound.

**Mignotte bound — proof strategy using existing Mathlib results:**

Mathlib already has the heavy analysis. The key results (all in
`Mathlib.Analysis.Polynomial.MahlerMeasure`, by Fabrizio Barroero):

1. **Mahler measure definition and root-product formula:**
   `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`:
   `M(p) = ‖leadingCoeff‖ * ∏ max(1, ‖αᵢ‖)`

2. **Multiplicativity:** `mahlerMeasure_mul`:
   `M(p * q) = M(p) * M(q)`

3. **Coefficient bound:** `norm_coeff_le_choose_mul_mahlerMeasure`:
   `‖p.coeff n‖ ≤ C(deg p, n) * M(p)`

4. **Landau-type bounds:**
   - `mahlerMeasure_le_sum_norm_coeff`: `M(p) ≤ ‖p‖₁`
   - `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`:
     `M(p) ≤ √(deg+1) * ‖p‖_∞`
   - The classical `M(p) ≤ ‖p‖₂` is not stated separately but is an
     intermediate step in the proof of the sqrt bound (via Parseval
     from `Mathlib.Analysis.Polynomial.Fourier`).

The Mignotte bound proof is then short glue:

```lean
theorem mignotte_bound (f g : Polynomial ℤ) (hg : g ∣ f) (j : ℕ) :
    |(g.coeff j : ℤ)| ≤ Nat.choose g.natDegree j * ‖f‖₂
```

Proof outline:
- Map `f`, `g` to `Polynomial ℂ` via `Polynomial.map (Int.castRingHom ℂ)`.
- `g ∣ f` gives `f = g * h`, so `M(f) = M(g) * M(h)` by
  `mahlerMeasure_mul`.
- `M(h) ≥ 1` for nonzero integer polynomials: the leading coefficient
  has `‖leadingCoeff‖ ≥ 1` (it's a nonzero integer), and
  `one_le_prod_max_one_norm_roots` gives `∏ max(1, ‖αᵢ‖) ≥ 1`.
  So `M(h) = ‖lc‖ * ∏ max(1, ‖αᵢ‖) ≥ 1`, hence `M(g) ≤ M(f)`.
- `norm_coeff_le_choose_mul_mahlerMeasure` gives
  `‖g.coeff j‖ ≤ C(deg g, j) * M(g) ≤ C(deg g, j) * M(f)`.
- `M(f) ≤ ‖f‖₂` by Parseval + Jensen (extractable from the proof of
  `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`, or proved
  directly via `sum_sq_norm_coeff_eq_circleAverage`).

The proof is short glue, mostly coercion bookkeeping between
`ℤ[X]` and `ℂ[X]`.

**Open Mathlib PR:** https://github.com/leanprover-community/mathlib4/pull/33463
("Mahler Measure for other rings", Kevin Wilson, open since Jan 2026)
extends the Mahler measure definition beyond `ℂ[X]`. If this lands,
the `ℤ → ℂ` coercion step becomes cleaner.

**Candidates for upstreaming to Mathlib:**

The following results are natural additions to Mathlib's Mahler measure
library and should be contributed independently of this project:

- `mahlerMeasure_le_l2norm`: the classical Landau inequality
  `M(p) ≤ ‖p‖₂ := √(∑ ‖coeff i‖²)`, currently only an intermediate
  step inside the proof of `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`.
  Extracting it as a standalone theorem is straightforward.
- `one_le_mahlerMeasure_of_intPoly`: `M(p) ≥ 1` for nonzero integer
  polynomials (leading coeff has norm ≥ 1, root product ≥ 1).
- `mahlerMeasure_dvd_le`: `g ∣ f → M(g) ≤ M(f)` for integer
  polynomials. Immediate from multiplicativity + the above.
- The Mignotte bound itself: `‖g.coeff j‖ ≤ C(deg g, j) * M(f)`
  when `g ∣ f` over ℤ. This is a one-line corollary but would be a
  useful named result.

These are all small PRs that complete the Mahler measure story for
the most common use case (integer polynomials).

---

### hex-berlekamp (factoring over F_p, depends on hex-poly-fp + hex-matrix + hex-gfq-ring)

Berlekamp's algorithm and Rabin's irreducibility test for polynomials
over finite fields.

**Contents:**
- **Berlekamp matrix**: compute `Q_f`, the matrix of the Frobenius map
  `h ↦ h^p mod f` in the basis `{1, x, ..., x^{n-1}}`
- **Berlekamp kernel**: nullspace of `Q_f - I` (from hex-matrix)
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

**Proof split (computational vs correctness):**

`hex-berlekamp` proves the computational invariant (no Mathlib):
```lean
theorem prod_berlekampFactor (f : FpPoly p) (hf : squareFree f) :
    (berlekampFactor f).prod = f
```

This is a loop invariant: each GCD step preserves
`factors.prod * remaining = f`. Uses hex-poly's division/GCD
correctness (`d ∣ g → d * (g / d) = g`).

The deeper correctness theorems live in `hex-berlekamp-mathlib`:
```lean
theorem irreducible_of_mem_berlekampFactor (f : FpPoly p) (hf : squareFree f) :
    ∀ g ∈ berlekampFactor f, Irreducible g

theorem rabin_irreducible (f : FpPoly p) (hf : f.degree = n) :
    rabinTest f = true ↔ Irreducible f
```

These require Euclidean domain theory (coprime divisibility,
irreducible ⟹ prime, factor theorem) — all available from Mathlib
via the ring equivalence `FpPoly p ≃+* Polynomial (ZMod p)`. See
hex-berlekamp-mathlib below for the proof strategy.

**References:**
- Berlekamp, "Factoring Polynomials Over Large Finite Fields,"
  *Math. Comp.* 24(111), 1970, pp. 713-735 (freely available from AMS)
- Shoup, *A Computational Introduction to Number Theory and Algebra*,
  2nd ed. (2009), chs. 20-21 (free PDF at `shoup.net/ntb/`)
- Knuth, *TAOCP* Vol. 2, section 4.6.2
- Isabelle AFP entry "Berlekamp_Zassenhaus"
  (Divason-Joosten-Thiemann-Yamada, 2016; JAR 2019). Browsable at
  `isa-afp.org/entries/Berlekamp_Zassenhaus.html`.

---

### hex-berlekamp-mathlib (depends on hex-berlekamp + hex-poly-mathlib + hex-mod-arith-mathlib + Mathlib)

Proves the full correctness of Berlekamp's algorithm and Rabin's test
by transferring to `Polynomial (ZMod p)` and using Mathlib's Euclidean
domain theory.

**Key theorems:**
```lean
theorem irreducible_of_mem_berlekampFactor (f : FpPoly p) (hf : squareFree f) :
    ∀ g ∈ berlekampFactor f, Irreducible g

theorem rabin_irreducible (f : FpPoly p) (hf : f.degree = n) :
    rabinTest f = true ↔ Irreducible f

instance [Fact (Nat.Prime p)] : DecidablePred (Irreducible · : Polynomial (ZMod p) → Prop)
```

**Proof strategy for `irreducible_of_mem_berlekampFactor`:**

The proof proceeds by contrapositive: if `g` is reducible, we
construct a nonconstant Berlekamp kernel element, which means the
algorithm would have split `g` further.

The proof works through the ring equivalence
`FpPoly p ≃+* Polynomial (ZMod p)` (from hex-poly-mathlib +
hex-mod-arith-mathlib). Steps 1-3 use Euclidean domain theory
that Mathlib provides for `Polynomial (ZMod p)`:

- `Polynomial.dvd_iff_isRoot` (factor theorem)
- `IsCoprime.mul_dvd` (coprime divisibility)
- `Irreducible.prime` (irreducible ⟹ prime in UFD)
- `ZMod.pow_card` (Fermat's little theorem for `ZMod p`)

**Step 1. `X^p - X = ∏_{c ∈ F_p} (X - c)` over F_p.**
From Fermat's little theorem (already in `hex-arith`): every `c ∈ F_p`
is a root of `X^p - X`, there are `p` of them, and `deg(X^p - X) = p`,
so the factorization follows by leading coefficient comparison.

**Step 2. Reducible squarefree polynomials have nonconstant kernel
elements.**
If `g` is reducible, write `g = a * b` with `a, b` nontrivial. Since
`g` is squarefree, `gcd(a, b) = 1`. By `polyCRT` (from `hex-poly`),
find `h` with `h ≡ 0 (mod a)` and `h ≡ 1 (mod b)`, reduced mod `g`.
Then:
- `a | h`, so `a | h^p - h` (since `0^p - 0 = 0`)
- `b | h - 1`, so `b | h^p - h` (since `1^p - 1 = 0`)
- `gcd(a, b) = 1`, so `g = a * b | h^p - h`

And `h` is nonconstant mod `g`: `h ≡ 0 (mod a)` but `h ≡ 1 (mod b)`.

Note: this does NOT require factoring `g` into irreducibles — any
nontrivial coprime splitting works.

**Step 3. Nonconstant kernel elements produce nontrivial GCD splits.**
If `g` is squarefree and `g | h^p - h` with `h` nonconstant mod `g`:
by step 1, `h^p - h = ∏_{c ∈ F_p} (h - c)`, so
`g | ∏_{c ∈ F_p} (h - c)`. The factors `(h - c)` are pairwise coprime
(they differ by nonzero constants). Each irreducible factor of `g`
divides exactly one `(h - c)`, so `g = ∏_{c ∈ F_p} gcd(g, h - c)`
(using `g` squarefree). Since `h` is nonconstant, the irreducible
factors of `g` distribute among at least two values of `c`, so
`gcd(g, h - c)` is nontrivial for some `c`.

**Step 4. Kernel of `f` surjects onto kernel of `g | f`.**
If `g | f` with `gcd(g, f/g) = 1` (which holds since `f` is
squarefree), then for any `h` with `g | h^p - h`, `polyCRT` gives
`h'` with `h' ≡ h (mod g)` and `h' ≡ 0 (mod f/g)`. Then
`g | h'^p - h'` and `(f/g) | h'^p - h'`, so `f | h'^p - h'`.
The element `h' mod f` is in the Berlekamp kernel of `f` and maps to
`h mod g` under reduction.

**Step 5. Completeness.**
The algorithm computes a basis `{h₁, …, hₖ}` of the Berlekamp kernel
of `f` (nullspace of `Q_f - I`), then for each `h_i` and each
`c ∈ F_p`, splits current factors via `gcd(factor, h_i - c)`.

After processing all basis elements, every output factor `g` has the
property that each `h_i` is constant mod `g`. This is because: when
`h_i` was processed, either `g` itself was in the factor list and
wasn't split by `h_i` (so `g | h_i - c₀` for some `c₀`), or an
ancestor `g' ⊇ g` was present with `g' | h_i - c₀`, giving
`g | h_i - c₀` too.

Since every basis element is constant on `g`, and the basis spans the
kernel of `f`, the image of the kernel of `f` under reduction mod `g`
consists only of constants. By surjectivity (step 4), the kernel of `g`
itself consists only of constants. If `g` were reducible, step 2 would
give a nonconstant kernel element — contradiction. So `g` is
irreducible.

**Note on representatives.** The `polyCRT` construction builds
`h = u · t · b + v · s · a`, which can have degree up to
`deg(a) + deg(b) - 1`, exceeding `deg(f)` or `deg(g)`. All
operations should use `h mod f` (or `h mod g`) as the representative.
This is safe because kernel membership depends only on the residue
class: `f | h^p - h` iff `f | (h mod f)^p - (h mod f)`, and GCD
computations respect reduction: `gcd(g, h - c) = gcd(g, (h mod g) - c)`.

**Rabin's test** additionally requires finite field theory (also in
Mathlib): quotient by irreducible is a field, `|GF(p^n)| = p^n`,
Lagrange's theorem on the multiplicative group.

---

### hex-conway (Conway polynomial database, depends on hex-berlekamp)

Conway polynomials are canonical irreducible polynomials `C(p, n)` for
each prime `p` and degree `n`, satisfying compatibility conditions
across degree divisors: if `m | n`, then the image of a root of
`C(p, n)` under the norm map `GF(p^n) → GF(p^m)` is a root of
`C(p, m)`. This ensures that embeddings `GF(p^m) ↪ GF(p^n)` are
coherent.

**Two sources of Conway polynomials:**

1. **Hardcoded database** — commonly used `(p, n)` pairs, sourced from
   Frank Lübeck's tables. Each entry comes with a Lean-checked
   irreducibility certificate (from hex-berlekamp) and a proof of
   compatibility with all divisor-degree entries already in the database.

2. **On-demand computation** — for `(p, n)` pairs not in the database,
   search for the lexicographically smallest monic irreducible polynomial
   of degree `n` over `F_p` satisfying the compatibility condition with
   all `C(p, m)` for `m | n`. This uses hex-berlekamp for irreducibility
   testing. The result is deterministic (the definition of Conway
   polynomial specifies "lexicographically smallest").

**API:**
```lean
def conwayPoly (p n : Nat) : FpPoly p

theorem conwayPoly_irreducible (p n : Nat) : Irreducible (conwayPoly p n)
theorem conwayPoly_compat (p m n : Nat) (h : m ∣ n) : ...
```

`conwayPoly` always returns a result (falling back to on-demand
computation). For small `(p, n)` it hits the hardcoded table; for
larger values it computes. The caller doesn't need to know which path
was taken.

**hex-gfq** then defines `GFq p n := FiniteField p (conwayPoly p n)
(conwayPoly_irreducible p n)`. When a user asks for `GF(p^n)`, the
Conway polynomial is chosen automatically.

---

### hex-gfq-ring (GF(q) as a ring, depends on hex-poly-fp)

Quotient ring `F_p[x] / (f)` for an arbitrary polynomial `f` over `F_p`.

**Contents:**
- `PolyQuotient p f` — elements of `F_p[x] / (f)`, represented as
  polynomials of degree < deg(f)
- Ring operations: addition, multiplication (multiply then reduce mod f),
  negation
- `Lean.Grind.CommRing` instance

This does NOT require `f` to be irreducible — the quotient is always a
ring. When `f` is irreducible, the quotient is a field, but that's
hex-gfq-field's job.

**Key properties:**
- Ring axioms
- `reduce (a * b) = reduce a * reduce b` (well-definedness of quotient)
- Canonical representative: degree < deg(f)

---

### hex-gfq-field (GF(q) as a field, depends on hex-berlekamp)

Extends `hex-gfq-ring` with field operations when the modulus is
irreducible. Takes any irreducible polynomial as parameter — not tied
to Conway polynomials.

**Contents:**
- `FiniteField p f (hirr : Irreducible f)` — the field `F_p[x]/(f)`,
  where `f` is any irreducible polynomial over `F_p`
- Multiplicative inverse via extended GCD in `F_p[x]`
- `Lean.Grind.Field` instance
- `IsCharP (FiniteField p f hirr) p`

The irreducibility proof `hirr` comes from hex-berlekamp (either via
the algorithm or via a certificate). This type is not tied to Conway
polynomials — any irreducible polynomial works (e.g. AES uses
`x^8 + x^4 + x^3 + x + 1` over `F_2`). For a canonical choice, see
hex-gfq.

**Key properties:**
- `inv a * a = 1` for `a ≠ 0`
- `Fintype (FiniteField p f hirr)` with `card = p ^ f.degree`
- Frobenius automorphism: `frob(a) = a^p`

---

### hex-gfq (convenience wrapper, depends on hex-gfq-field + hex-conway)

Thin wrapper providing `GFq p n` — the canonical finite field with
`p^n` elements, using the Conway polynomial as the irreducible modulus.

```lean
def GFq (p n : Nat) := FiniteField p (conwayPoly p n) (conwayPoly_irreducible p n)
```

The user writes `GFq 2 8` and gets `GF(2^8)` with no further choices.
For non-Conway models (e.g. AES's `x^8 + x^4 + x^3 + x + 1`), use
`FiniteField` directly from hex-gfq-field.

---

### hex-gfq-mathlib (depends on hex-gfq + Mathlib)

Proves `GFq p n ≃+* GaloisField p n` (Mathlib's Galois field).
Proof strategy: apply `FiniteField.ringEquivOfCardEq` from Mathlib,
which just needs `Fintype.card (GFq p n) = Fintype.card (GaloisField p n)`.
Both sides equal `p ^ n` — Mathlib has `GaloisField.card` and we need
`card_finiteField` from hex-gfq-field.

---

### hex-hensel (Hensel lifting, depends on hex-poly-fp + hex-poly-z)

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
    (g' * h').congr f (p^(k+1))

theorem hensel_extends_fst (f g h : ZPoly) (p k : Nat) :
    (henselLift f g h p k).1.congr g (p^k)

theorem hensel_extends_snd (f g h : ZPoly) (p k : Nat) :
    (henselLift f g h p k).2.congr h (p^k)

theorem hensel_degree_fst (f g h : ZPoly) (p k : Nat) :
    (henselLift f g h p k).1.degree = g.degree

theorem hensel_degree_snd (f g h : ZPoly) (p k : Nat) :
    (henselLift f g h p k).2.degree = h.degree

-- The deep theorem: uniqueness of Hensel lifting.
theorem hensel_unique_fst (f g h g' h' : ZPoly) (p k : Nat) :
    g.leadingCoeff = 1 →
    (g * h).congr f (p^k) →
    (g' * h').congr f (p^k) →
    g.congr g' p →
    h.congr h' p →
    g.coprimeModP h p →
    g = g'

theorem hensel_unique_snd (f g h g' h' : ZPoly) (p k : Nat) :
    g.leadingCoeff = 1 →
    (g * h).congr f (p^k) →
    (g' * h').congr f (p^k) →
    g.congr g' p →
    h.congr h' p →
    g.coprimeModP h p →
    h = h'
```

**Strategy**: Start with linear lifting (simpler invariant, easier to
verify). Add quadratic as an optimization proved equivalent via uniqueness.

---

### hex-gram-schmidt (Gram-Schmidt orthogonalization, depends on hex-matrix)

Gram-Schmidt orthogonalization for integer and rational matrices.
Provides the GS orthogonal basis, coefficient matrix, Gram determinants,
and update formulas under row operations. Used by hex-lll but logically
independent of LLL.

**Design:**
- Two sub-namespaces: `GramSchmidt.Int` (integer input matrices) and
  `GramSchmidt.Rat` (rational input matrices).
- Functions return matrices, not indexed single-entry functions:
  `basis b` returns a `Matrix Rat n m` (all GS vectors at once),
  `coeffs b` returns a `Matrix Rat n n` (lower-unitriangular).
- `Nat` indices with explicit bounds hypotheses, not `Fin`.
- `basis` and `coeffs` are `noncomputable` (rational division); they
  exist for the proof layer. `gramDet` and `scaledCoeffs` are computable.

**API:**

```lean
namespace ComputationalAlgebra.GramSchmidt.Int

/-- The Gram-Schmidt orthogonal basis. Row i is the projection of b.row i
    onto the orthogonal complement of span(b.row 0, ..., b.row (i-1)). -/
noncomputable def basis (b : Matrix Int n m) : Matrix Rat n m

/-- The Gram-Schmidt coefficients. Lower-unitriangular: entry (i,j) is
    ⟨b[i], (basis b)[j]⟩ / ⟨(basis b)[j], (basis b)[j]⟩ for j < i,
    1 on diagonal, 0 above. -/
noncomputable def coeffs (b : Matrix Int n m) : Matrix Rat n n

/-- The k-th Gram determinant: det of the k×k leading Gram submatrix.
    gramDet b 0 = 1 by convention. Returns Nat (always a positive integer
    for independent bases; an internal helper computes the Int determinant
    and the public API wraps via .toNat). -/
def gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Nat

/-- All Gram determinants as a vector. -/
def gramDetVec (b : Matrix Int n m) : Vector Nat (n + 1)

/-- Scaled GS coefficients (the ν-values): entry (i,j) = d_{j+1} * μ_{i,j}
    for j < i. Always integers (integrality lemma). -/
def scaledCoeffs (b : Matrix Int n m) : Matrix Int n n

end ComputationalAlgebra.GramSchmidt.Int

namespace ComputationalAlgebra.GramSchmidt.Rat

noncomputable def basis (b : Matrix Rat n m) : Matrix Rat n m
noncomputable def coeffs (b : Matrix Rat n m) : Matrix Rat n n
def gramDet (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Rat

end ComputationalAlgebra.GramSchmidt.Rat
```

**Key properties** (stated for `GramSchmidt.Int`; `Rat` analogous):
```lean
theorem basis_zero (b : Matrix Int n m) (hn : 0 < n) :
    (basis b).row 0 = (b.row 0).map Int.cast

theorem basis_orthogonal (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ((basis b).row i).dotProduct ((basis b).row j) = 0

theorem basis_decomposition (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (b.row i).map Int.cast =
      (basis b).row i +
      Finset.sum (Finset.range i) fun j =>
        (coeffs b)[i][j] • (basis b).row j

theorem coeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (coeffs b)[i][i] = 1

theorem coeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : j > i) :
    (coeffs b)[i][j] = 0

theorem basis_span (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    -- span(basis b 0, ..., basis b i) = span(b 0, ..., b i)
    sorry

theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : b.independent) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) =
      Finset.prod (Finset.range k) fun j =>
        ((basis b).row j).dotProduct ((basis b).row j)

theorem gramDet_pos (b : Matrix Int n m)
    (hli : b.independent) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk

theorem basis_normSq (b : Matrix Int n m)
    (hli : b.independent) (k : Nat) (hk : k < n) :
    ((basis b).row k).dotProduct ((basis b).row k) =
      (gramDet b (k + 1) (by omega) : Rat) / (gramDet b k (by omega) : Rat)

theorem scaledCoeffs_eq (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    (scaledCoeffs b)[i][j] =
      gramDet b (j + 1) (by omega) * (coeffs b)[i][j]

theorem normSq_latticeVec_ge_min_basis_normSq
    (b : Matrix Int n m) (hli : b.independent)
    (v : Vector Int m) (hv : b.memLattice v) (hv' : v ≠ 0) :
    ∃ i, i < n ∧
      ((basis b).row i).dotProduct ((basis b).row i) ≤
        (v.dotProduct v : Rat)
```

**Update formulas under row operations:**
- Size reduction (`b_k ← b_k - r * b_j`, `j < k`): GS basis unchanged,
  coefficients update as `coeffs[k][j] ← coeffs[k][j] - r`.
- Swap (`b_k ↔ b_{k-1}`): explicit formulas for new basis, coefficients,
  and Gram determinants (see hex-lll section for the full formulas).

**Integrality of scaledCoeffs.** (Von zur Gathen & Gerhard, Lemma 16.7.)
scaledCoeffs[i][j] = gramDet (j+1) * coeffs[i][j] can be expressed as
a (j+1) × (j+1) determinant: take the Gram matrix G_{j+1} and replace
its last column (inner products with b[j]) by inner products with b[i]:

    scaledCoeffs[i][j] = det | <b[0],b[0]>  ...  <b[0],b[j-1]>   <b[0],b[i]> |
                              | <b[1],b[0]>  ...  <b[1],b[j-1]>   <b[1],b[i]> |
                              |   ...        ...    ...            ...       |
                              | <b[j],b[0]>  ...  <b[j],b[j-1]>   <b[j],b[i]> |

Since all inner products are integers, this determinant is an integer.
(The formula follows from Cramer's rule on G_{j+1} * x = g, where g
is the column of inner products with b[i]: coeffs[i][j] =
det(G_{j+1} with last column replaced) / gramDet (j+1). Multiplying by
gramDet (j+1) gives the integer determinant above.)

**Why divisions are exact under swap.** scaledCoeffs[i][j] =
gramDet (j+1) * coeffs[i][j] and the coeffs values are always
expressible as ratios of integer determinants with denominator
gramDet (j+1). After a swap, the new coeffs values have the same
property with the new gramDet values. The algebraic identities can
also be verified directly by substituting the definitions and using
the fact that Gram determinants of sub-lattices are always integers.

**File organization:**
- `GramSchmidt.lean` — definitions, orthogonality, span, decomposition,
  lower bound lemma
- `GramSchmidtUpdate.lean` — how GS quantities change under size
  reduction (unchanged) and swap (explicit update formulas)
- `GramSchmidtInt.lean` — `scaledCoeffs`, integrality, `gramDetVec`,
  exact division under swap

Mathlib's `gramSchmidt` works over inner product spaces and does not
track coefficients or update formulas, so it cannot be used in the
computational core. The `hex-gram-schmidt-mathlib` bridge proves
that `GramSchmidt.Int.basis` corresponds to Mathlib's `gramSchmidt`.

---

### hex-lll (LLL lattice basis reduction, depends on hex-gram-schmidt)

**Completely independent of the polynomial libraries.** Can be developed
in parallel from day one.

**Contents:**
- LLL algorithm using the d-representation (all integer arithmetic,
  no rationals stored; rational GS quantities as `noncomputable` projections)
- Size reduction (ensure |coeffs[i][j]| ≤ 1/2)
- Lovász condition check and basis swap

**Definitions:**
```lean
/-- v is in the integer lattice spanned by the rows of b. -/
def Matrix.memLattice (b : Matrix Int n m) (v : Vector Int m) : Prop :=
    ∃ c : Vector Int n, b.mulVec c = v

/-- The rows of b are linearly independent (all Gram determinants positive). -/
def Matrix.independent (b : Matrix Int n m) : Prop :=
    ∀ k : Fin n, 0 < det (b.gramMatrix.submatrix k)

/-- Squared L2 norm of an integer vector. -/
def Vector.normSq (v : Vector Int m) : Int := v.dotProduct v
```

`dotProduct`, `normSq`, and `gramMatrix` live in hex-matrix.
`memLattice`, `independent`, and `isLLLReduced` live in hex-lll.

**delta-LLL-reduced.** A basis b is delta-LLL-reduced (for
delta in (1/4, 1]) if it satisfies two conditions:

1. **Size-reduced:** |(coeffs b)[i][j]| <= 1/2 for all 0 <= j < i < n.

2. **Lovász condition:** For all 0 <= i < n-1:
       delta * ||(basis b)[i]||^2 <= ||(basis b)[i+1]||^2 + (coeffs b)[i+1][i]^2 * ||(basis b)[i]||^2

   Equivalently: (delta - (coeffs b)[i+1][i]^2) * ||(basis b)[i]||^2 <= ||(basis b)[i+1]||^2

**Key properties.** All theorems require
`hδ : 1/4 < δ`, `hδ' : δ ≤ 1`, `hn : 1 ≤ n`, and
`hli : b.independent`.

`δ > 1/4` so that `α = 1/(δ - 1/4)` is well-defined and positive.
`δ ≤ 1` for termination (the Lovász failure condition is strict, so
each swap gives `gramDet b' k < δ · gramDet b k ≤ gramDet b k`,
strictly decreasing the potential even at `δ = 1`). Linear
independence ensures all Gram determinants `gramDet b k > 0`, which
is needed for the GS orthogonalization to exist and for the
scaledCoeffs denominators to be nonzero.

```lean
theorem lll_same_lattice (b : Matrix Int n m) (δ : Rat) ... :
    (lll b δ ...).memLattice v ↔ b.memLattice v

theorem lll_reduced (b : Matrix Int n m) (δ : Rat) ... :
    isLLLReduced (lll b δ ...) δ

theorem lll_short_vector (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1)
    (hn : 1 ≤ n) (hli : b.independent)
    (v : Vector Int m) :
    b.memLattice v → v ≠ 0 →
    (lll b δ hδ hδ' hn hli).row 0 |>.normSq ≤ α^(n-1) * v.normSq
  where α := 1 / (δ - 1/4)
```

The short vector guarantee with `δ = 3/4` gives `‖b₁‖ ≤ 2^{(n-1)/2} · λ₁`.

---

#### LLLState and algorithm

The algorithm operates on a single integer state: basis vectors,
Gram determinants, and scaled GS coefficients. The rational GS
quantities (coeffs, basis norms) are never stored or computed at
runtime — they exist only as `noncomputable` projections for use
in proofs.

```lean
/-- LLL state. All fields are integers; no rationals stored. -/
structure LLLState (n m : Nat) where
  b : Matrix Int n m            -- basis vectors
  ν : Matrix Int n n            -- ν[i][j] = d[j+1] * coeffs[i][j] for j < i
  d : Vector Nat (n + 1)        -- Gram determinants d_0, ..., d_n
  ν_eq : ∀ i j, j < i → (ν[i][j] : Rat) = (d[j + 1] : Rat) * (GramSchmidt.Int.coeffs b)[i][j]
  d_eq : ∀ i, d[i] = GramSchmidt.Int.gramDet b i ‹_›

/-- Recover a single rational GS coefficient from the integer state.
    Marked noncomputable: exists only for the proof layer. -/
noncomputable def LLLState.gramSchmidtCoeff (s : LLLState n m) (i j : Nat) : Rat :=
  (s.ν[i][j] : Rat) / (s.d[j + 1] : Rat)

-- Use https://github.com/leanprover/lean4/pull/13200 when available.
def LLLState.potential (s : LLLState n m) : Nat :=
  s.d[1:n].foldl (· * ·) 1    -- d_1 * d_2 * ... * d_{n-1}
```

**Size reduction.** Size-reduce b[k] against b[k-1], ..., b[0].
Updates b and ν; d is unchanged (basis is unchanged by size
reduction).

```lean
def LLLState.sizeReduce (s : LLLState n m) (k : Nat) : LLLState n m := sorry
```

For j = k-1 downto 0: if 2 * |ν[k][j]| > d[j+1] (i.e., |coeffs[k][j]| > 1/2):

    r := Int.fdiv (2 * ν[k][j] + d[j+1]) (2 * d[j+1])
    b[k] := b[k] - r * b[j]
    ν[k][l] := ν[k][l] - r * ν[j][l]    for l < j
    ν[k][j] := ν[k][j] - r * d[j+1]

**Swap step.** Swap b[k] and b[k-1], updating ν and d.

```lean
def LLLState.swapStep (s : LLLState n m) (k : Nat) : LLLState n m := sorry
```

Let B = ν[k][k-1]. After swapping b[k] and b[k-1]:

*d update:*

    d[k]' = (d[k+1] * d[k-1] + B^2) / d[k]

This division is exact (see integrality section below). All other
d[i] are unchanged.

*ν updates* (Cohen Algorithm 2.6.3, 0-indexed):

ν[k][k-1]' = B (unchanged: (scaledCoeffs b')[k][k-1] = (scaledCoeffs b)[k][k-1]).

For j < k-1: ν[k-1][j] and ν[k][j] simply swap.

For i > k, the two affected columns update simultaneously:

    ν[i][k-1]' = (ν[i][k-1] * d[k]' + ν[i][k] * B) / d[k]
    ν[i][k]'   = (ν[i][k] * d[k-1] - ν[i][k-1] * B) / d[k]

(Verify precise formulas for i > k against Cohen Algorithm 2.6.3 or
von zur Gathen & Gerhard Algorithm 16.10 during implementation.) All
divisions are exact (see integrality section below). Only d[k] changes
among d-values, and only ν values with one index equal to k or k-1
change.

**Main loop.** The Lovász condition in integer form (see integrality
section below for derivation) is:

    d[k+1] * d[k-1] + ν[k][k-1]^2 >= δ * d[k]^2

For δ = p/q rational, this becomes a comparison of integers (no
division): `q * (d[k+1] * d[k-1] + ν[k][k-1]^2) >= p * d[k]^2`.

```lean
def lllAux (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hind : s.b.independent)
    (hk : 1 ≤ k) (hkn : k ≤ n) : Matrix Int n m :=
  if h : k = n then s.b
  else
    let s := s.sizeReduce k
    -- Check Lovász condition (integer arithmetic, no division):
    if δ.den * (s.d[k+1] * s.d[k-1] + s.ν[k][k-1]^2) ≥ δ.num * s.d[k]^2 then
      -- Lovász holds: advance
      lllAux s (k + 1) δ hδ hδ' ‹_› (by omega) (by omega)
    else
      -- Lovász fails: swap and decrement
      let s := s.swapStep k
      lllAux s (max (k - 1) 1) δ hδ hδ' ‹_› (by omega) (by omega)
termination_by (s.potential, n - k)
-- Termination uses only ν_eq, d_eq, and correctness of sizeReduce/swapStep.
-- Advance: sizeReduce preserves d (GS vectors unchanged), so potential
--   unchanged; n - k decreases.
-- Swap: the failing Lovász condition (read from d and ν via d_eq/ν_eq)
--   gives d[k]' < δ * d[k] ≤ d[k]; potential strictly decreases.

def lll (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) : Matrix Int n m :=
  lllAux ⟨b, GramSchmidt.Int.scaledCoeffs b, GramSchmidt.Int.gramDetVec b, sorry, sorry⟩
    1 δ hδ hδ' hind (by omega) (by omega)
```

The swap bound `potential_initial ≤ (maxNormSq b)^{n*(n-1)/2}` follows
from Hadamard's inequality: `gramDet b k ≤ prod_{i<k} ||b[i]||^2 ≤
(maxNormSq b)^k`.

---

#### Loop invariant

At the top of the loop with current index k, expressed in terms of
the noncomputable projections `s.gramSchmidtCoeff` and the GS vectors
(which are mathematical functions of `s.b`, not stored):

(I1) b[0], ..., b[n-1] is a basis of the same lattice L as the input.
(I2) basis[0], ..., basis[n-1] and coeffs[i][j] are the correct
     Gram-Schmidt orthogonalization of the current basis. (This is
     captured by `s.ν_eq` and `s.d_eq`, which assert that the stored
     integer values track the mathematical GS quantities.)
(I3) **Size-reduced below k:** |s.gramSchmidtCoeff i j| <= 1/2 for all j < i < k.
(I4) **Lovász condition below k:** for all 0 <= i < k-1,
     (delta - (s.gramSchmidtCoeff (i+1) i)^2) * ||basis[i]||^2 <= ||basis[i+1]||^2.
(I5) 1 <= k <= n.

Together, (I3) and (I4) say: the first k vectors form a
delta-LLL-reduced basis of the sublattice they span.

**Size-reduction sub-invariant.** The inner loop
`for j in [k-1, k-2, ..., 0]` has its own invariant, parameterized
by the current column j.
After processing column j (and before processing j-1), the following
hold in addition to (I1)-(I5):

(SR1) |s.gramSchmidtCoeff k l| <= 1/2 for all l with j <= l < k.
(SR2) s.gramSchmidtCoeff k l is unchanged for l < j.
(SR3) All basis[i] vectors are unchanged (size reduction preserves GS).
(SR4) The lattice is unchanged (unimodular row operations).

Before processing j = k-1, (SR1) is vacuous (no columns have been
processed yet). After processing column j, (SR1) holds for j <= l < k.
At exit (all columns processed), (SR1) gives
|s.gramSchmidtCoeff k l| <= 1/2 for all l < k, establishing (I3) for the new k.

**Preservation of the outer invariant:**

- *Size reduction (full inner loop):* Preserves the lattice (I1) and
  all basis[i] (I2) — these follow from (SR3)+(SR4). Establishes
  |s.gramSchmidtCoeff k j| <= 1/2 for all j < k — this follows from (SR1) at
  exit. The Lovász conditions for indices < k-1 are unaffected (I4),
  since only coeffs values in row k change and the basis[i] are unchanged.

- *Advance (k <- k+1):* Only happens when the Lovász condition holds
  at index k-1. Combined with the already-established conditions
  below k-1, we now have all conditions below k, so (I3)+(I4) hold
  for the new k.

- *Swap (b[k] <-> b[k-1], k <- max(k-1, 1)):* Preserves the lattice
  (I1). Changes only basis[k-1] and basis[k] among the GS vectors (I2).
  The Lovász conditions for indices < k-2 are unaffected (I4). We
  lose the size-reduction guarantee at the new k (the swapped vector
  may not be size-reduced), so (I3) is only claimed for indices
  below the new k. We may need to re-check at the new k, hence
  decrementing k.

---

#### Short vector bound proof

The proof has three steps.

**Step 1: Consecutive GS norm bound.** From the Lovász condition
with the size-reduction guarantee |coeffs[i+1][i]| <= 1/2:

    (delta - coeffs[i+1][i]^2) * ||basis[i]||^2 <= ||basis[i+1]||^2
    (delta - 1/4) * ||basis[i]||^2 <= ||basis[i+1]||^2

Set alpha = 1 / (delta - 1/4). Then:

    ||basis[i]||^2 <= alpha * ||basis[i+1]||^2

By telescoping (induction on the gap):

    ||basis[0]||^2 <= alpha^i * ||basis[i]||^2     for all 0 <= i < n

More usefully:

    ||basis[0]||^2 <= alpha^{n-1} * min_{0 <= i < n} ||basis[i]||^2

**Step 2: Lower bound lemma.** For any nonzero lattice vector
v in L, we have:

    ||v||^2 >= min_{0 <= i < n} ||basis[i]||^2

*Proof.* Write v = sum_{i=0}^{n-1} a_i * b[i] with a_i in Z (not all
zero). Let k be the largest index with a_k != 0. Expand in the
GS basis:

    v = sum_{i=0}^{k} a_i * b[i]
      = sum_{i=0}^{k} a_i * (basis[i] + sum_{j<i} coeffs[i][j] * basis[j])
      = sum_{i=0}^{k} c_i * basis[i]

for some real coefficients c_i, where crucially c_k = a_k (because
b[k] = basis[k] + sum_{j<k} coeffs[k][j] * basis[j], and no later
b[i] contributes to the basis[k] component). Since a_k is a nonzero
integer, |c_k| >= 1.

By orthogonality of the basis[i]:

    ||v||^2 = sum_{i=0}^{k} c_i^2 * ||basis[i]||^2
            >= c_k^2 * ||basis[k]||^2
            >= ||basis[k]||^2
            >= min_{0 <= i < n} ||basis[i]||^2     QED

**Step 3: Combining.** For any nonzero v in L:

    ||b[0]||^2 = ||basis[0]||^2              (b[0] = basis[0] by definition)
              <= alpha^{n-1} * min_i ||basis[i]||^2    (Step 1)
              <= alpha^{n-1} * ||v||^2                 (Step 2)

This gives the main theorem:

    ||b[0]||^2 <= alpha^{n-1} * ||v||^2

for any nonzero lattice vector v, where alpha = 1/(delta - 1/4).

For the standard choice delta = 3/4, alpha = 2, and we get
||b[0]|| <= 2^{(n-1)/2} * lambda_1(L).

---

#### Integrality and integer representation

This section provides the proofs that the integer update formulas
are correct and that all divisions are exact. (The integrality of
scaledCoeffs itself is proved in hex-gram-schmidt; here we derive
the LLL-specific update formulas.)

**Derivation of the integer Lovász condition.** The rational Lovász
condition rearranged (following Cohen, section 2.6.3):

    ||basis[k]||^2 + coeffs[k][k-1]^2 * ||basis[k-1]||^2 >= delta * ||basis[k-1]||^2

Substitute ||basis[i]||^2 = gramDet (i+1)/gramDet i and
coeffs[k][k-1] = scaledCoeffs[k][k-1]/gramDet k:

    gramDet (k+1)/gramDet k + (scaledCoeffs[k][k-1]/gramDet k)^2 * (gramDet k/gramDet (k-1))
        >= delta * (gramDet k/gramDet (k-1))

Multiply through by gramDet k * gramDet (k-1) (both positive):

    gramDet (k+1) * gramDet (k-1) + scaledCoeffs[k][k-1]^2 >= delta * gramDet k^2

(Negated for the swap trigger: swap when this fails.)

**Correctness of size-reduction updates.** The rational size-reduction
step sets coeffs[k][j] <- coeffs[k][j] - r (and
coeffs[k][l] <- coeffs[k][l] - r * coeffs[j][l] for l < j).
Multiplying through by gramDet (j+1) (resp. gramDet (l+1)) gives
the scaledCoeffs update formulas:

    scaledCoeffs[k][l] <- scaledCoeffs[k][l] - r * scaledCoeffs[j][l]    for l < j
    scaledCoeffs[k][j] <- scaledCoeffs[k][j] - r * gramDet (j+1)

The gramDet values are unchanged because size reduction preserves the
GS basis.

**Rounding.** Define:

```lean
/-- Round to nearest integer (ties round up). -/
def Rat.round (q : Rat) : Int := (q + 1/2).floor
-- Key property: |q - q.round| ≤ 1/2 (from floor_le and lt_floor_add_one)
```

The rounding value r = round(coeffs[k][j]) =
round(scaledCoeffs[k][j] / gramDet (j+1)) is computed as
`Int.fdiv (2 * scaledCoeffs[k][j] + gramDet (j+1)) (2 * gramDet (j+1))`,
which is pure integer arithmetic since gramDet (j+1) > 0.

**Correctness of swap updates.** Let b' be the basis after swapping
b[k] and b[k-1], and let B = (scaledCoeffs b)[k][k-1]. The gramDet
update:

    gramDet b' k = (gramDet b (k+1) * gramDet b (k-1) + B^2) / gramDet b k

follows from the determinant identity for the Gram matrix after the
swap. The scaledCoeffs updates for i > k:

    (scaledCoeffs b')[i][k-1] = ((scaledCoeffs b)[i][k-1] * gramDet b' k + (scaledCoeffs b)[i][k] * B) / gramDet b k
    (scaledCoeffs b')[i][k]   = ((scaledCoeffs b)[i][k] * gramDet b (k-1) - (scaledCoeffs b)[i][k-1] * B) / gramDet b k

follow from substituting the definitions scaledCoeffs = gramDet * coeffs
into the rational coeffs update formulas and simplifying. For j < k-1,
(scaledCoeffs b')[k-1][j] and (scaledCoeffs b')[k][j] are
(scaledCoeffs b)[k][j] and (scaledCoeffs b)[k-1][j] respectively
(simply swapped).

---

#### Termination

**Potential function.** Define:

    D = prod_{i=1}^{n-1} gramDet i

This is the product of the first n-1 Gram determinants. Equivalently:

    D = prod_{k=0}^{n-2} ||basis[k]||^{2(n-1-k)}

(since gramDet i = prod_{j=0}^{i-1} ||basis[j]||^2, each
||basis[k]||^2 appears in gramDet i for i = k+1, k+2, ..., n-1,
contributing exponent n-1-k to the product). Since the basis remains
linearly independent throughout (unimodular row operations preserve
independence), each gramDet i is a positive integer, so D >= 1.

**Size reduction preserves D.** Size reduction does not change
basis b, so all gramDet b i (and hence D) are unchanged.

**Each swap decreases D.** Let b' be the basis after swapping b[k]
and b[k-1], with the Lovász condition failing:

    gramDet b' k = (gramDet b (k+1) * gramDet b (k-1) + (scaledCoeffs b)[k][k-1]^2) / gramDet b k

The Lovász condition fails, meaning:

    gramDet b (k+1) * gramDet b (k-1) + (scaledCoeffs b)[k][k-1]^2 < delta * (gramDet b k)^2

So gramDet b' k < delta * gramDet b k. Since only gramDet at
index k changes (gramDet b' i = gramDet b i for i ≠ k), and
gramDet b k appears exactly once in the product D:

    D' = D * (gramDet b' k / gramDet b k) < D * delta

Since D >= 1 is a positive integer and each swap strictly decreases
D (because gramDet b' k < gramDet b k for integer gramDet values),
the algorithm terminates with at most D_initial - 1 swaps.

For delta < 1, the stronger bound gramDet b' k < delta * gramDet b k
gives D' < delta * D, so:

    #swaps <= log_{1/delta}(D_initial)

Using D_initial <= (max_i ||b[i]||^2)^{n(n-1)/2} (by Hadamard's
inequality: gramDet b k <= prod_{i<k} ||b[i]||^2 <= (maxNormSq b)^k):

    #swaps <= n(n-1)/2 * log(max_i ||b[i]||^2) / log(1/delta)

This is polynomial in n and the bit-size of the input. (At delta = 1,
termination is still guaranteed but the log bound degenerates; the
integer bound #swaps <= D_initial - 1 applies instead.)

**Lean formalization strategy for termination:** Use well-founded
recursion on the pair (D, n - k), lexicographically ordered. Each
iteration either decreases D (swap) or increases k (advance), and
k is bounded by n.

---

#### Formalization strategy: single-state architecture

**Approach.** Unlike the Isabelle AFP formalization (Bottesch et al.,
ITP 2018, JAR 2020), which uses a two-layer bisimulation between a
rational specification and an integer implementation, we use a
single-state design. The `LLLState` stores only integers (b, ν, d).
The rational GS quantities are recovered via `noncomputable`
projections (`LLLState.gramSchmidtCoeff`, and similarly for
`||(basis b)[k]||^2 = gramDet b (k+1) / gramDet b k`), which exist
only for the proof layer.

The key advantage: no bisimulation proof is needed. There is one
state, one algorithm, and the correctness proofs unfold the
`noncomputable` definitions to connect integer update formulas
to their rational counterparts (see integrality section above).
The `noncomputable` marker makes it syntactically impossible for the
rational quantities to leak into the executable code.

**Proof structure.** For each step (size-reduce, swap, advance):
1. Show the integer update formulas preserve `ν_eq` and `d_eq`
   (i.e., the stored integers still track the GS quantities of
   the new basis). This uses the integrality derivations above.
2. Show the loop invariant (I1)–(I5) is preserved. This uses the
   `noncomputable` projections to state conditions in their natural
   rational form.
3. The short vector bound is proved purely in terms of mathematical
   GS properties. Termination uses the integer state directly (the
   potential is a product of gramDet values, and the swap decrease
   follows from the integer Lovász failure).

**Highest-risk proof areas:**

- **Swap update formulas.** The explicit formulas for how
  `GramSchmidt.Int.basis`, `GramSchmidt.Int.coeffs`, `gramDet`, and
  `scaledCoeffs` change under a swap are the most error-prone part.
  Each formula must be verified algebraically and the exact division
  proofs must be discharged.
- **Exact division under swap.** Proving that
  `(gramDet b (k+1) * gramDet b (k-1) + (scaledCoeffs b)[k][k-1]^2) / gramDet b k`
  and the scaledCoeffs update divisions are exact requires the
  determinant-based integrality arguments from hex-gram-schmidt.

**Prior art.** The Isabelle AFP formalization (~14,800 lines across
14 modules) uses a two-layer bisimulation: `LLL.thy` defines a
rational specification with loop invariant proofs, and `LLL_Impl.thy`
defines the d-representation implementation with a step-refinement
proof connecting the two. Their `upw` ("update needed") boolean in
the outer invariant avoids exposing the size-reduction inner-loop
index. We chose not to follow this architecture, instead using a
single integer state with `noncomputable` projections.

**References:**
- Lenstra, Lenstra, Lovász, "Factoring polynomials with rational
  coefficients," *Math. Ann.* 261, 1982, pp. 515-534 (original paper)
- Von zur Gathen & Gerhard, *Modern Computer Algebra*, 3rd ed., 2013,
  ch. 16 (primary reference for formalization)
- Cohen, *A Course in Computational Algebraic Number Theory*, 1993,
  section 2.6 (integral LLL algorithm)
- Galbraith, *Mathematics of Public Key Cryptography*, 2012, ch. 17
  (good exposition; free PDF at math.auckland.ac.nz/~sgal018/crypto-book/)
- Bottesch et al., "A Formalization of the LLL Basis Reduction
  Algorithm," ITP 2018 (Isabelle formalization, conference version)
- Bottesch et al., "Formalizing the LLL Basis Reduction Algorithm and
  the LLL Factorization Algorithm in Isabelle/HOL," *J. Automated
  Reasoning* 64, 2020, pp. 1-42 (Isabelle formalization, journal version)
- Nguyen & Stehlé, "Floating-Point LLL Revisited," EUROCRYPT 2005
  (L^2 algorithm; not needed for our formalization but relevant context)

---

### hex-gram-schmidt-mathlib (depends on hex-gram-schmidt + Mathlib)

Proves that `GramSchmidt.Int.basis` corresponds to Mathlib's
`gramSchmidt`. Mathlib's version works over inner product spaces and
returns a family of vectors; ours returns a `Matrix Rat n m`. The
bridge proves they agree on each row.

---

### hex-lll-mathlib (depends on hex-lll + Mathlib)

Connects hex-lll to Mathlib's linear algebra:
- Lattice corresponds to a `Submodule ℤ`
- Short vector bound holds with respect to Mathlib's `norm`

---

### hex-berlekamp-zassenhaus (the capstone)

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

---

### hex-berlekamp-zassenhaus-mathlib (depends on hex-berlekamp-zassenhaus + hex-poly-z-mathlib)

Instantiates the conditional correctness theorems from
hex-berlekamp-zassenhaus (which take an abstract coefficient bound)
with the Mignotte bound from hex-poly-z-mathlib, giving unconditional
results:
```lean
theorem factor_product (f : ZPoly) :
    (factor f (mignotteBound f)).prod = f

theorem factor_irreducible (f : ZPoly) :
    ∀ g ∈ factor f (mignotteBound f), Irreducible g

theorem factor_unique (f : ZPoly) (gs hs : List ZPoly) :
    gs.prod = f → hs.prod = f →
    (∀ g ∈ gs, Irreducible g) → (∀ h ∈ hs, Irreducible h) →
    gs ~ hs  -- multiset equality up to associates
```

Also connects to Mathlib's `Polynomial ℤ` and provides
`Decidable (Irreducible f)` for `f : Polynomial ℤ`.

This library is thin — the hard work is split between
hex-berlekamp-zassenhaus (algorithmic correctness, Mathlib-free) and
hex-poly-z-mathlib (the Mignotte bound).

---

## Development phases

Development has three kinds of work: **`def` implementations**,
**`theorem` statements** (with `sorry` proofs), and **`theorem` proofs**
(filling in the `sorry`s). The first two must follow the DAG; the
third is fully parallelizable.

**`def` implementations and `theorem` statements** must follow the
DAG — both need their transitively referenced `def`s to already have
implementations. `theorem` proofs can be `sorry` at this stage.

**`theorem` proofs** are fully parallelizable. A proof can begin as
soon as the theorem is stated and all transitively referenced `def`s
have implementations. Proofs in different libraries — or even within
the same library — have no ordering constraints.

### Implementation dependencies

Each library with its immediate dependencies:

- **hex-arith** — (none)
- **hex-poly** — (none)
- **hex-matrix** — (none)
- **hex-mod-arith** — hex-arith
- **hex-gram-schmidt** — hex-matrix
- **hex-lll** — hex-gram-schmidt
- **hex-poly-fp** — hex-poly, hex-mod-arith
- **hex-poly-z** — hex-poly
- **hex-berlekamp** — hex-poly-fp, hex-matrix, hex-gfq-ring
- **hex-hensel** — hex-poly-fp, hex-poly-z
- **hex-conway** — hex-berlekamp
- **hex-gfq-ring** — hex-poly-fp
- **hex-gfq-field** — hex-berlekamp
- **hex-gfq** — hex-gfq-field, hex-conway
- **hex-berlekamp-zassenhaus** — hex-berlekamp, hex-hensel, hex-lll

Mathlib bridge libraries (each also depends on Mathlib):

- **hex-mod-arith-mathlib** — hex-mod-arith
- **hex-poly-mathlib** — hex-poly
- **hex-poly-z-mathlib** — hex-poly-z, hex-poly-mathlib
- **hex-matrix-mathlib** — hex-matrix
- **hex-gram-schmidt-mathlib** — hex-gram-schmidt
- **hex-lll-mathlib** — hex-lll
- **hex-berlekamp-mathlib** — hex-berlekamp
- **hex-hensel-mathlib** — hex-hensel
- **hex-gfq-mathlib** — hex-gfq
- **hex-berlekamp-zassenhaus-mathlib** — hex-berlekamp-zassenhaus, hex-poly-z-mathlib

LLL is completely independent of the polynomial pipeline. The only
point of contact is at the very top (Berlekamp-Zassenhaus).

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

`PolyOps` for operations (including `dropZeros`), `LawfulPolyOps` for
ring axioms + `dropZeros` properties. The `-mathlib` bridge library proves
`CanonicalPoly P ≃+* Polynomial R` where
`CanonicalPoly P := { p : P // dropZeros p = p }`.

---

## Practical applications

**Cryptographic field construction:** To build `GF(2^128)` for AES, you
need an irreducible polynomial of degree 128 over `F_2`. With
hex-berlekamp, produce a Lean proof that it's irreducible.

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

## Repository structure

Separate repos per library, with each repo containing a single Lake
package. This gives clean dependency management and allows independent
versioning. The cost is cross-repo development friction, but:

- Lake handles git dependencies natively
- Each library is small enough to stabilize independently
- Mathlib bridge libraries can track Mathlib's toolchain independently
  of the computational libraries
- Contributors can work on hex-lll without pulling hex-poly

For the initial bootstrapping phase, a single monorepo with multiple
Lake packages is acceptable, splitting into separate repos once the
APIs stabilize.

## Conformance testing

Every computational library is tested against reference implementations:

1. Generate random inputs (polynomials, lattice bases, etc.)
2. Compute results in both Lean and a reference (FLINT via FFI, SageMath,
   fpLLL) and compare
3. For polynomial factoring, cross-check factorizations against FLINT
   and verify certificates produced by the Lean algorithms

SageMath and FLINT are used for **testing**, not for algorithms — the
distinction is that all computation runs in Lean, and external tools
only serve as an independent oracle for conformance checking.

---

## Further work

Items not on the critical path for Berlekamp-Zassenhaus, but worth
doing once the core is stable.

**Hermite normal form.** Row reduction over `Int`: upper triangular
with positive pivots, entries above each pivot in `[0, pivot)`. Uses
extended GCD to create pivots without division: given entries `a`, `b`
in the same column, compute `(g, s, t)` with `s * a + t * b = g`,
then apply the 2×2 row transformation `[[s, t], [-b/g, a/g]]` to
zero out `b` and replace `a` with `g`. Reduce entries above each pivot
modulo the pivot. The result is unique. Returns `RowEchelonData`; an
`IsHNF` Prop-valued structure extending `IsEchelonForm` (parallel to
`IsRREF`) certifies correctness, with HNF-specific fields:
- Each pivot is positive
- Entries above each pivot are in `[0, pivot)`
- `det transform = 1 ∨ det transform = -1`

HNF requires extended GCD, which lives in hex-arith. Since
hex-matrix currently has no dependencies, HNF would either need:
extended GCD upstreamed into Lean 4 stdlib, a new dependency
hex-matrix → hex-arith, or a separate library (e.g.
`hex-matrix-hermite` depending on both hex-matrix and hex-arith).

**Smith normal form.** Diagonal form obtained by both row and column
operations over a principal ideal domain. The diagonal entries satisfy
`d₁ | d₂ | ⋯ | dᵣ` (divisibility chain). Useful for computing the
structure of finitely generated abelian groups and solving integer
linear systems. Like HNF, requires extended GCD and is not needed for
Berlekamp-Zassenhaus.

**Sylvester's identity (hex-matrix).** The Desnanot-Jacobi identity
relating minors of a matrix. A useful result in its own right, and
gives an alternative proof that `bareiss M = det M`: show by induction
that Bareiss step k computes the leading k×k minor
`det(M[1..k, 1..k])`, with Sylvester's identity as the inductive step.

**Generic Bareiss over integral domains (hex-matrix).** Generalize
Bareiss from `Int` to any integral domain with a data-carrying exact
division operation (`ediv : α → α → α` with `b ∣ a → ediv a b * b = a`);
for `Int` this is `Int.divExact`
and no zero divisors (`a * b = 0 → a = 0 ∨ b = 0`).
