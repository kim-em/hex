# lean-algebra — Verified Computational Algebra in Lean 4

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

These would live in `lean-gmp-extras` or be proposed as upstream additions
to the Lean runtime.

---

## Libraries

- **lean-arith** — extended GCD, Barrett/Montgomery reduction, binomial coefficients, Fermat's little theorem
- **lean-poly** — polynomial typeclass interface + dense `Array`-backed representation
- **lean-matrix** — dense matrices as `Vector (Vector R m) n`, RREF, Bareiss determinant, span, nullspace
- **lean-mod-arith** — `ZMod64 p`: `UInt64`-backed arithmetic in `Z/pZ`
- **lean-poly-fp** — polynomials over `F_p`, Frobenius map, square-free decomposition
- **lean-poly-z** — polynomials over `Z`, content/primitive part, Mignotte bound
- **lean-berlekamp** — Berlekamp factoring and Rabin irreducibility test over `F_p`
- **lean-hensel** — Hensel lifting from `mod p` to `mod p^k`
- **lean-lll** — LLL lattice basis reduction
- **lean-berlekamp-zassenhaus** — complete factoring of `Z[x]`
- **lean-conway** — Conway polynomial database
- **lean-gfq-ring** — quotient ring `F_p[x]/(f)`
- **lean-gfq-field** — field structure when `f` is irreducible
- **lean-gfq** — convenience wrapper: `GFq p n` using Conway polynomials

## Library DAG

Three independent roots: lean-poly, lean-arith, lean-matrix.

```
      lean-poly     lean-arith      lean-matrix
       /     \          |            /       \
      /       \     lean-mod-arith  /    lean-lll
     /         \       /           /         /
lean-poly-z  lean-poly-fp         /         /
     \        /       \          /         / 
     lean-hensel      lean-berlekamp      /
               \        |                /
                lean-berlekamp-zassenhaus
```

Additional libraries (finite field construction):
```
  lean-poly-fp        lean-berlekamp
       |              /      |
  lean-gfq-ring      /   lean-conway
          \         /       /
        lean-gfq-field     /
                 \        /
                  lean-gfq
```

**Mathlib bridge libraries** (each depends on a computational lib + Mathlib,
proving correspondence with Mathlib's mathematical definitions):

- **lean-mod-arith-mathlib** — `ZMod64 p ≃+* ZMod p`
- **lean-poly-mathlib** — `DensePoly R ≃+* Polynomial R` via `LawfulPolyOps`
- **lean-matrix-mathlib** — matrix equivalence, `det` agreement, rank = `Matrix.rank`, nullspace = `LinearMap.ker`, row ops = transvections
- **lean-poly-z-mathlib** — proves Mignotte bound valid (via FTA, Mahler measure, Landau's inequality)
- **lean-berlekamp-mathlib** — `Decidable (Irreducible f)` for `Polynomial (ZMod p)`
- **lean-hensel-mathlib** — Hensel lifting corresponds to Mathlib's `Polynomial` factoring
- **lean-lll-mathlib** — lattice = `Submodule ℤ`, GSO = `gramSchmidt`, short vector bound
- **lean-gfq-mathlib** — `GFq p n ≃+* GaloisField p n`
- **lean-berlekamp-zassenhaus-mathlib** — proves Mignotte bound (via FTA), unconditional factoring correctness, `Decidable (Irreducible f)` for `Polynomial ℤ`

---

## Library descriptions

### lean-arith (foundation, no dependencies)

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

### lean-matrix (foundation, no dependencies)

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
where `/` is `Int.div` — the division is always exact (no remainder).

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

### lean-matrix-mathlib (depends on lean-matrix + Mathlib)

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

### lean-mod-arith (modular arithmetic, depends on lean-arith)

Arithmetic in `Z/nZ` with `UInt64`-backed coefficients.

**Contents:**
- `ZMod64 (p : Nat)` — a `UInt64` with proof `val.toNat < p`
- Addition, subtraction, multiplication (using Barrett/Montgomery from
  lean-arith for the `UInt64` modular operations)
- Inversion via extended GCD (for prime moduli)
- Exponentiation by squaring
- `Lean.Grind.CommRing (ZMod64 p)` instance and `IsCharP (ZMod64 p) p`

**Key properties:**
- Ring axioms proved directly from the modular arithmetic definitions.
  Associativity and distributivity of multiplication reduce to
  `Nat.mod` properties via Barrett/Montgomery correctness from
  lean-arith.
- `inv a * a = 1` when `Nat.Coprime a.val p` — via extended GCD
  from lean-arith: `s * a + t * p = 1` gives `s mod p` as the inverse.
- No zero divisors for prime `p`: `a * b = 0 → a = 0 ∨ b = 0` — via
  Euclid's lemma from lean-arith.
- Fermat's little theorem: `a ^ p = a` — lifts directly from
  `Nat.pow_prime_mod` in lean-arith.

**Note:** `Fin n` already has `Lean.Grind.CommRing` and `IsCharP`. We
build `ZMod64` for performance (Barrett reduction instead of naive modular
arithmetic) and for cleaner API (explicit prime parameter, field operations).

---

### lean-mod-arith-mathlib (depends on lean-mod-arith + Mathlib)

Proves `ZMod64 p ≃+* ZMod p`. This means any Mathlib theorem about
`ZMod p` transfers to `ZMod64 p`, and any computation with `ZMod64 p`
is known correct in the mathematical sense.

---

### lean-poly (polynomial interface + dense representation, no dependencies)

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

### lean-poly-mathlib (depends on lean-poly + Mathlib)

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
- Mignotte bound computation: `|gⱼ| ≤ C(k,j) · ‖f‖₂` for any degree-k
  factor `g | f` in `Z[x]`. The computation is just binomial coefficients
  and the 2-norm of `f`'s coefficients. The proof that the bound is valid
  requires complex analysis (Mahler measure, Landau's inequality) and
  lives in `lean-poly-z-mathlib`.
- Reduction modulo p: `ZPoly → FpPoly p`

**Key properties:**
- `content(f * g) = content(f) * content(g)` (Gauss)
- `primitivePart(f)` is primitive (content = 1)

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

### lean-berlekamp-mathlib (depends on lean-berlekamp + Mathlib)

Connects the computational `Irreducible` to Mathlib's `Irreducible`
in `Polynomial (ZMod p)`. The payoff: a `Decidable` instance for
`Irreducible` on `Polynomial (ZMod p)`, backed by a verified algorithm.

```lean
instance [Fact (Nat.Prime p)] : DecidablePred (Irreducible · : Polynomial (ZMod p) → Prop)
```

---

### lean-conway (Conway polynomial database, depends on lean-poly-fp + lean-berlekamp)

Conway polynomials are canonical irreducible polynomials `C(p, n)` for
each prime `p` and degree `n`, satisfying compatibility conditions
across degree divisors: if `m | n`, then the image of a root of
`C(p, n)` under the norm map `GF(p^n) → GF(p^m)` is a root of
`C(p, m)`. This ensures that embeddings `GF(p^m) ↪ GF(p^n)` are
coherent.

**Two sources of Conway polynomials:**

1. **Hardcoded database** — commonly used `(p, n)` pairs, sourced from
   Frank Lübeck's tables. Each entry comes with a Lean-checked
   irreducibility certificate (from lean-berlekamp) and a proof of
   compatibility with all divisor-degree entries already in the database.

2. **On-demand computation** — for `(p, n)` pairs not in the database,
   search for the lexicographically smallest monic irreducible polynomial
   of degree `n` over `F_p` satisfying the compatibility condition with
   all `C(p, m)` for `m | n`. This uses lean-berlekamp for irreducibility
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

**lean-gfq** then defines `GFq p n := FiniteField p (conwayPoly p n)
(conwayPoly_irreducible p n)`. When a user asks for `GF(p^n)`, the
Conway polynomial is chosen automatically.

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
irreducible. Takes any irreducible polynomial as parameter — not tied
to Conway polynomials.

**Contents:**
- `FiniteField p f (hirr : Irreducible f)` — the field `F_p[x]/(f)`,
  where `f` is any irreducible polynomial over `F_p`
- Multiplicative inverse via extended GCD in `F_p[x]`
- `Lean.Grind.Field` instance
- `IsCharP (FiniteField p f hirr) p`

The irreducibility proof `hirr` comes from lean-berlekamp (either via
the algorithm or via a certificate). This type is not tied to Conway
polynomials — any irreducible polynomial works (e.g. AES uses
`x^8 + x^4 + x^3 + x + 1` over `F_2`). For a canonical choice, see
lean-gfq.

**Key properties:**
- `inv a * a = 1` for `a ≠ 0`
- `Fintype (FiniteField p f hirr)` with `card = p ^ f.degree`
- Frobenius automorphism: `frob(a) = a^p`

---

### lean-gfq (convenience wrapper, depends on lean-gfq-field + lean-conway)

Thin wrapper providing `GFq p n` — the canonical finite field with
`p^n` elements, using the Conway polynomial as the irreducible modulus.

```lean
def GFq (p n : Nat) := FiniteField p (conwayPoly p n) (conwayPoly_irreducible p n)
```

The user writes `GFq 2 8` and gets `GF(2^8)` with no further choices.
For non-Conway models (e.g. AES's `x^8 + x^4 + x^3 + x + 1`), use
`FiniteField` directly from lean-gfq-field.

---

### lean-gfq-mathlib (depends on lean-gfq + Mathlib)

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

### lean-lll-mathlib (depends on lean-lll + Mathlib)

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

### lean-berlekamp-zassenhaus-mathlib (depends on lean-berlekamp-zassenhaus + Mathlib)

Proves the Mignotte bound is valid (via FTA, Mahler measure, Landau's
inequality from Mathlib) and instantiates the conditional correctness
theorems to get unconditional results:
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

- **lean-arith** — (none)
- **lean-poly** — (none)
- **lean-matrix** — (none)
- **lean-mod-arith** — lean-arith
- **lean-lll** — lean-matrix
- **lean-poly-fp** — lean-poly, lean-mod-arith
- **lean-poly-z** — lean-poly
- **lean-berlekamp** — lean-poly-fp, lean-matrix
- **lean-hensel** — lean-poly-fp, lean-poly-z
- **lean-conway** — lean-poly-fp, lean-berlekamp
- **lean-gfq-ring** — lean-poly-fp
- **lean-gfq-field** — lean-gfq-ring, lean-berlekamp
- **lean-gfq** — lean-gfq-field, lean-conway
- **lean-berlekamp-zassenhaus** — lean-berlekamp, lean-hensel, lean-lll

Mathlib bridge libraries (each also depends on Mathlib):

- **lean-mod-arith-mathlib** — lean-mod-arith
- **lean-poly-mathlib** — lean-poly
- **lean-poly-z-mathlib** — lean-poly-z
- **lean-matrix-mathlib** — lean-matrix
- **lean-lll-mathlib** — lean-lll
- **lean-berlekamp-mathlib** — lean-berlekamp
- **lean-hensel-mathlib** — lean-hensel
- **lean-gfq-mathlib** — lean-gfq
- **lean-berlekamp-zassenhaus-mathlib** — lean-berlekamp-zassenhaus, lean-poly-z-mathlib

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

## Repository structure

Separate repos per library, with each repo containing a single Lake
package. This gives clean dependency management and allows independent
versioning. The cost is cross-repo development friction, but:

- Lake handles git dependencies natively
- Each library is small enough to stabilize independently
- Mathlib bridge libraries can track Mathlib's toolchain independently
  of the computational libraries
- Contributors can work on lean-lll without pulling lean-poly

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

HNF requires extended GCD, which lives in lean-arith. Since
lean-matrix currently has no dependencies, HNF would either need:
extended GCD upstreamed into Lean 4 stdlib, a new dependency
lean-matrix → lean-arith, or a separate library (e.g.
`lean-matrix-hermite` depending on both lean-matrix and lean-arith).

**Smith normal form.** Diagonal form obtained by both row and column
operations over a principal ideal domain. The diagonal entries satisfy
`d₁ | d₂ | ⋯ | dᵣ` (divisibility chain). Useful for computing the
structure of finitely generated abelian groups and solving integer
linear systems. Like HNF, requires extended GCD and is not needed for
Berlekamp-Zassenhaus.

**Sylvester's identity (lean-matrix).** The Desnanot-Jacobi identity
relating minors of a matrix. A useful result in its own right, and
gives an alternative proof that `bareiss M = det M`: show by induction
that Bareiss step k computes the leading k×k minor
`det(M[1..k, 1..k])`, with Sylvester's identity as the inductive step.

**Generic Bareiss over integral domains (lean-matrix).** Generalize
Bareiss from `Int` to any integral domain with a data-carrying exact
division operation (`ediv : α → α → α` with `b ∣ a → ediv a b * b = a`)
and no zero divisors (`a * b = 0 → a = 0 ∨ b = 0`).
