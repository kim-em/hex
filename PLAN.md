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
     \        /       |          /         /
     lean-hensel  lean-gfq-ring /         /
               \       |       /         /
                \  lean-berlekamp       /
                 \      |              /
                  lean-berlekamp-zassenhaus
```

Additional libraries (finite field construction):
```
        lean-berlekamp
         /          \
  lean-gfq-field  lean-conway
         \          /
          lean-gfq
```

**Mathlib bridge libraries** (each depends on a computational lib + Mathlib,
proving correspondence with Mathlib's mathematical definitions):

- **lean-mod-arith-mathlib** — `ZMod64 p ≃+* ZMod p`
- **lean-poly-mathlib** — `DensePoly R ≃+* Polynomial R` via `LawfulPolyOps`
- **lean-matrix-mathlib** — matrix equivalence, `det` agreement, rank = `Matrix.rank`, nullspace = `LinearMap.ker`, row ops = transvections
- **lean-poly-z-mathlib** — `DensePoly Int ≃+* Polynomial ℤ`, Mignotte bound (via Mathlib's Mahler measure)
- **lean-berlekamp-mathlib** — `Decidable (Irreducible f)` for `Polynomial (ZMod p)`
- **lean-hensel-mathlib** — Hensel lifting corresponds to Mathlib's `Polynomial` factoring
- **lean-lll-mathlib** — lattice = `Submodule ℤ`, GSO = `gramSchmidt`, short vector bound
- **lean-gfq-mathlib** — `GFq p n ≃+* GaloisField p n`
- **lean-berlekamp-zassenhaus-mathlib** — unconditional factoring correctness, `Decidable (Irreducible f)` for `Polynomial ℤ`

---

## Library descriptions

### lean-arith (no dependencies)

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
with `h ≡ u (mod a)` and `h ≡ v (mod b)`. Used by lean-berlekamp
(steps 2, 3, 5) and potentially lean-hensel and lean-gfq-ring.

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
  lives in `lean-poly-z-mathlib`.
- Reduction modulo p: `ZPoly → FpPoly p`

**Key properties:**
- `content(f * g) = content(f) * content(g)` (Gauss)
- `primitivePart(f)` is primitive (content = 1)

---

### lean-poly-z-mathlib (depends on lean-poly-z + Mathlib)

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

### lean-berlekamp (factoring over F_p, depends on lean-poly-fp + lean-matrix + lean-gfq-ring)

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

**Proof strategy:**

The key theorems are:
```lean
theorem prod_berlekampFactor (f : FpPoly p) (hf : squareFree f) :
    (berlekampFactor f).prod = f

theorem irreducible_of_mem_berlekampFactor (f : FpPoly p) (hf : squareFree f) :
    ∀ g ∈ berlekampFactor f, Irreducible g
```

`prod_berlekampFactor` is straightforward — a loop invariant: each GCD
step preserves `factors.prod * remaining = f`.

`irreducible_of_mem_berlekampFactor` is the hard theorem. The proof
proceeds by contrapositive: if `g` is reducible, we construct a
nonconstant Berlekamp kernel element, which means the algorithm would
have split `g` further.

**Step 1. `X^p - X = ∏_{c ∈ F_p} (X - c)` over F_p.**
From Fermat's little theorem (already in `lean-arith`): every `c ∈ F_p`
is a root of `X^p - X`, there are `p` of them, and `deg(X^p - X) = p`,
so the factorization follows by leading coefficient comparison.

**Step 2. Reducible squarefree polynomials have nonconstant kernel
elements.**
If `g` is reducible, write `g = a * b` with `a, b` nontrivial. Since
`g` is squarefree, `gcd(a, b) = 1`. By `polyCRT` (from `lean-poly`),
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

**Note on representatives.** CRT-constructed polynomials may have
degree `≥ deg(f)`. Reduce mod `f` (or mod `g`). Kernel membership is
preserved: `f | h^p - h` iff `f | (h mod f)^p - (h mod f)`. GCD
computations are preserved: `gcd(g, h - c) = gcd(g, (h mod g) - c)`.

The proof uses only concrete polynomial arithmetic: GCD, Bezout,
modular reduction, pairwise coprimality. No quotient ring machinery,
no abstract algebra. Everything is proved in `lean-berlekamp` without
Mathlib.

**`lean-berlekamp-mathlib` bridge:** ring equivalence
`FpPoly p ≃+* Polynomial (ZMod p)`, correspondence between the two
definitions of `Irreducible`, yielding
`DecidablePred (Irreducible · : Polynomial (ZMod p) → Prop)`.

Rabin's theorem:
```lean
theorem rabin_irreducible (f : FpPoly p) (hf : f.degree = n) :
    rabinTest f = true ↔ Irreducible f
```

**References:**
- Berlekamp, "Factoring Polynomials Over Large Finite Fields,"
  *Math. Comp.* 24(111), 1970, pp. 713-735 (freely available from AMS)
- Shoup, *A Computational Introduction to Number Theory and Algebra*,
  2nd ed. (2009), chs. 20-21 (free PDF at `shoup.net/ntb/`)
- Knuth, *TAOCP* Vol. 2, section 4.6.2
- Isabelle AFP entry "Berlekamp_Zassenhaus"
  (Divason-Joosten-Thiemann-Yamada, 2016; JAR 2019). They prove the
  full CRT ring isomorphism and dim(B) = number of factors; we avoid
  that entirely via the contrapositive argument. Browsable at
  `isa-afp.org/entries/Berlekamp_Zassenhaus.html`.

---

### lean-berlekamp-mathlib (depends on lean-berlekamp + Mathlib)

Connects the computational `Irreducible` to Mathlib's `Irreducible`
in `Polynomial (ZMod p)`. The payoff: a `Decidable` instance for
`Irreducible` on `Polynomial (ZMod p)`, backed by a verified algorithm.

```lean
instance [Fact (Nat.Prime p)] : DecidablePred (Irreducible · : Polynomial (ZMod p) → Prop)
```

---

### lean-conway (Conway polynomial database, depends on lean-berlekamp)

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

### lean-gfq-field (GF(q) as a field, depends on lean-berlekamp)

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
Proof strategy: apply `FiniteField.ringEquivOfCardEq` from Mathlib,
which just needs `Fintype.card (GFq p n) = Fintype.card (GaloisField p n)`.
Both sides equal `p ^ n` — Mathlib has `GaloisField.card` and we need
`card_finiteField` from lean-gfq-field.

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

Maintain GSO: gso_i and μ_{i,j} = ⟨b_i, gso_j⟩ / ⟨gso_j, gso_j⟩

k := 2
while k ≤ n:
  Size-reduce b_k: for j = k-1 downto 1, subtract round(μ_{k,j}) * b_j
  If Lovász condition holds (‖gso_k‖² ≥ (δ - μ²_{k,k-1}) · ‖gso_{k-1}‖²):
    k := k + 1
  Else:
    swap b_k and b_{k-1}, update GSO
    k := max(k-1, 2)
```

**Termination proof:**
- Potential function: `D = ∏ᵢ ‖gso_i‖^{2(n-i)}`
- D is a positive integer (integer lattice)
- Each swap decreases D by factor ≥ δ; size reduction doesn't change D
- At most `n(n-1)/2 · log(B) / log(1/δ)` swaps (polynomial bound)

**d-representation** (the Isabelle approach, avoids rationals):
Store `d_{i+1} · μ_{i,j}` where `d_i = det(Gram matrix of first i vectors)`.
All positive integers. No GCD, no fraction normalization.

**Key properties (all characterizing).** All theorems require
`hδ : 1/4 < δ`, `hδ' : δ ≤ 1`, and `hli : b.LinearIndependent`.
```lean
theorem lll_same_lattice (b : Basis n m) (δ : Rat) ... :
    lattice (lll b δ ...) = lattice b

theorem lll_reduced (b : Basis n m) (δ : Rat) ... :
    isLLLReduced (lll b δ ...) δ

theorem lll_short_vector (b : Basis n m) (δ : Rat) ...
    (v : LatVector m) :
    v ∈ lattice b → v ≠ 0 →
    ‖(lll b δ ...).head‖² ≤ α^(n-1) * ‖v‖²
  where α := 1 / (δ - 1/4)

theorem lll_swap_bound (b : Basis n m) (δ : Rat) ... :
    swapCount (lll b δ ...) ≤
      n * (n-1) / 2 * log₂(maxNormSq b) / log₂(1/δ)
```

The short vector guarantee with `δ = 3/4` gives `‖b₁‖ ≤ 2^{(n-1)/2} · λ₁`.

Uses stdlib `Rat` for the specification; d-representation `Int` for
computation.

**Proof strategy (research completed 2026-03-30):** See PROOFS.md
Section 2 for the complete analysis. Summary:

- **Two-layer architecture.** Layer 1 (specification): define LLL and
  prove the short vector bound using `Rat`-valued Gram-Schmidt.
  Layer 2 (implementation): the d-representation algorithm using only
  `Int`. A step-refinement lemma connects the layers — each step of
  the integer algorithm mirrors the corresponding rational step under
  an explicit state relation `dmu_{i,j} = d_{j+1} * μ_{i,j}`.
- **Gram-Schmidt API** lives inside `lean-lll` (files
  `GramSchmidt.lean`, `GramSchmidtUpdate.lean`, `GramSchmidtInt.lean`),
  not a separate library.
- **Highest-risk areas:** swap update formulas (algebraic verification
  + exact division proofs), rounding agreement at ±1/2 boundary
  between the two layers.

**Prior art:** Isabelle AFP formalization (Bottesch, Divasón, Haslbeck,
Joosten, Thiemann, Yamada; ITP 2018, JAR 2020), ~14,800 lines across
14 modules.

**References:**
- Von zur Gathen & Gerhard, *Modern Computer Algebra*, 3rd ed., 2013,
  ch. 16 (primary reference)
- Cohen, *A Course in Computational Algebraic Number Theory*, 1993,
  section 2.6 (integral LLL algorithm)
- Bottesch et al., "Formalizing the LLL Basis Reduction Algorithm and
  the LLL Factorization Algorithm in Isabelle/HOL," *J. Automated
  Reasoning* 64, 2020, pp. 1-42

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

### lean-berlekamp-zassenhaus-mathlib (depends on lean-berlekamp-zassenhaus + lean-poly-z-mathlib)

Instantiates the conditional correctness theorems from
lean-berlekamp-zassenhaus (which take an abstract coefficient bound)
with the Mignotte bound from lean-poly-z-mathlib, giving unconditional
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
lean-berlekamp-zassenhaus (algorithmic correctness, Mathlib-free) and
lean-poly-z-mathlib (the Mignotte bound).

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
- **lean-berlekamp** — lean-poly-fp, lean-matrix, lean-gfq-ring
- **lean-hensel** — lean-poly-fp, lean-poly-z
- **lean-conway** — lean-berlekamp
- **lean-gfq-ring** — lean-poly-fp
- **lean-gfq-field** — lean-berlekamp
- **lean-gfq** — lean-gfq-field, lean-conway
- **lean-berlekamp-zassenhaus** — lean-berlekamp, lean-hensel, lean-lll

Mathlib bridge libraries (each also depends on Mathlib):

- **lean-mod-arith-mathlib** — lean-mod-arith
- **lean-poly-mathlib** — lean-poly
- **lean-poly-z-mathlib** — lean-poly-z, lean-poly-mathlib
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
