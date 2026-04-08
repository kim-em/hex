# Proof Triage

Scratch space for researching proof strategies. Once a proof is
understood and vetted, it gets incorporated into PLAN.md (under the
relevant library section) and deleted from here.

---

## Tier 1: Major Theorems

### 6. Mignotte bound validity

```lean
-- In hex-poly-z-mathlib
theorem mignotte_bound (f g : Polynomial ℤ) (hg : g ∣ f) (j : ℕ) :
    |(g.coeff j : ℤ)| ≤ Nat.choose g.natDegree j * ‖f‖₂
```

Mathlib has all the heavy analysis.
The Mahler measure library (`Mathlib.Analysis.Polynomial.MahlerMeasure`,
by Fabrizio Barroero, merged Sep–Nov 2025) provides:

- `mahlerMeasure_mul`: `M(p * q) = M(p) * M(q)`
- `norm_coeff_le_choose_mul_mahlerMeasure`: `‖p.coeff n‖ ≤ C(deg, n) * M(p)`
- `one_le_prod_max_one_norm_roots`: `∏ max(1, ‖αᵢ‖) ≥ 1`
- `mahlerMeasure_le_sum_norm_coeff`: `M(p) ≤ ‖p‖₁`
- `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`: goes through
  `M(p) ≤ ‖p‖₂` as an intermediate step (via Parseval)

The proof is short glue: map to `ℂ[X]`, use multiplicativity to get
`M(g) ≤ M(f)` (since `M(h) ≥ 1` for integer polynomials), apply the
coefficient bound, then bound `M(f)` by `‖f‖₂`.

**Upstreaming to Mathlib:**
https://github.com/leanprover-community/mathlib4/pull/37349 adds
Landau's inequality (`mahlerMeasure_le_sqrt_sum_sq_norm_coeff`),
the monotonicity lemma (`le_mahlerMeasure_mul_right`), and the
Mignotte bound (`norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`)
to `Mathlib.Analysis.Polynomial.MahlerMeasure`. Once merged, the
hex-poly-z-mathlib proof reduces to mapping `ℤ[X] → ℂ[X]` and
applying these results.

**Other open Mathlib PR:** https://github.com/leanprover-community/mathlib4/pull/33463
(Mahler Measure for other rings) would simplify the `ℤ → ℂ` coercion
further.

---

## Tier 2: Substantial but More Tractable

### 7. Bareiss = det (`bareiss_eq_det`)

```lean
theorem bareiss_eq_det (M : Matrix Int n n) : bareiss M = det M
```

**The Bareiss recurrence:**
```
a^{(k+1)}_{ij} = (a^{(k)}_{kk} · a^{(k)}_{ij} − a^{(k)}_{ik} · a^{(k)}_{kj}) / a^{(k-1)}_{k-1,k-1}
```
with `a^{(0)} := M` and the convention `a^{(-1)}_{-1,-1} := 1`.
The final answer is `a^{(n-1)}_{n-1,n-1}`. Each division is exact
(proved as a corollary of the invariant below).

**Proof strategy: the bordered-minor invariant.**

Define the "bordered minor" for `k ≥ 0` and `i, j ≥ k`:
```
μ(k; i, j) := det M[rows 0..k-1 ∪ {i} | cols 0..k-1 ∪ {j}]
```
This is a `(k+1) × (k+1)` determinant. Note `μ(0; i, j) = M_{ij}`
(a 1×1 minor) and `μ(k; k, k) = det M[0..k | 0..k]` is the leading
principal `(k+1) × (k+1)` minor.

**Key invariant** (Bareiss's theorem):
```
∀ k ≥ 0, ∀ i, j ≥ k, a^{(k)}_{ij} = μ(k; i, j)
```

Extracting the result: at `k = n-1, i = j = n-1`, the invariant
gives `a^{(n-1)}_{n-1,n-1} = μ(n-1; n-1, n-1) = det M`. ∎

**Base case** (`k = 0`). `a^{(0)}_{ij} = M_{ij} = μ(0; i, j)`.

**Inductive step.** Assume the invariant holds at step `k`. We need:
```
μ(k+1; i, j) = (μ(k; k, k) · μ(k; i, j) − μ(k; i, k) · μ(k; k, j)) / μ(k-1; k-1, k-1)
```
Rearranged, this is the **Desnanot–Jacobi identity** applied to
the `(k+2) × (k+2)` bordered minor `M[0..k, i | 0..k, j]`:
```
μ(k+1; i, j) · μ(k-1; k-1, k-1) = μ(k; k, k) · μ(k; i, j)
                                − μ(k; i, k) · μ(k; k, j)
```

This is a single mathematical fact — the Desnanot–Jacobi identity —
applied at each step.

**Desnanot–Jacobi identity** (the hard lemma). For an `n × n` matrix
`A`, let `A_{i,j}` denote `A` with row `i` and column `j` deleted,
and `A_{i,j;k,l}` denote `A` with rows `i, k` and columns `j, l`
deleted. Then:
```
det(A) · det(A_{1,1;n,n}) = det(A_{1,1}) · det(A_{n,n})
                          − det(A_{1,n}) · det(A_{n,1})
```
This specializes to what we need: take `A = M[0..k, i | 0..k, j]`
(a `(k+2) × (k+2)` submatrix with rows 0..k, i and columns 0..k, j,
placed so that the "last" row/column is `i`/`j`). The four "corner"
minors `A_{1,1}, A_{n,n}, A_{1,n}, A_{n,1}` are the `(k+1)×(k+1)`
bordered minors `μ(k; ·, ·)` that appear in the Bareiss recurrence.
The "doubly-punctured" `A_{1,1;n,n}` is `μ(k-1; k-1, k-1)`, the
previous pivot.

**Proofs of Desnanot–Jacobi.** Three options:

1. **Via Jacobi's complementary minor theorem.** Jacobi: for
   invertible `M`, an `r × r` minor of `adjugate(M)` equals
   `det(M)^{r-1}` times the complementary `(n-r) × (n-r)` cominor
   of `M`. Apply with `r = 2` and rows/columns `{1, n}`: the 2×2
   minor of `adj(M)` at `(1, n) × (1, n)` equals
   `adj(M)_{1,1} · adj(M)_{n,n} − adj(M)_{1,n} · adj(M)_{n,1}`,
   and each factor unfolds via the cofactor formula (signs cancel
   because `(-1)^{1+n} · (-1)^{1+n} = 1`). The complementary minor
   is `M_{1,1;n,n}`. This gives Desnanot–Jacobi for invertible `M`,
   and extends to the general case by Zariski density / polynomial
   identity.
2. **Via Laplace expansion.** Expand both sides as sums over
   permutations and show they match term-by-term. Tedious but
   completely elementary.
3. **Via multilinear alternating forms.** Both sides are
   multilinear alternating in the rows of the matrix and agree on
   permutation matrices. This is the cleanest proof given Mathlib's
   `MultilinearMap` infrastructure, but setting up the ambient form
   is still work.

Likely path: start with Laplace expansion (no new infrastructure).
If it's too painful, switch to the Jacobi approach using Mathlib's
`Matrix.adjugate` and `Matrix.mul_adjugate`.

**Mathlib API available** (`Matrix.det` is defined via Leibniz, so
hex-matrix's `det` should correspond via the ring equivalence):
- `Matrix.det_apply`, `Matrix.det_succ_row_zero`, `Matrix.det_succ_column_zero`
  — cofactor expansion
- `Matrix.adjugate`, `Matrix.mul_adjugate`, `Matrix.adjugate_mul`
- `Matrix.det_updateRow_add`, `Matrix.det_updateRow_smul` — row-op
  determinant effects
- `Matrix.det_transpose`, `Matrix.det_mul`
- `Matrix.submatrix`, `Matrix.det_submatrix_equiv_self` — for
  stating minors
- Index manipulation: `Fin.succAbove`, `Matrix.submatrix_succAbove_succAbove`

**Mathlib PR in progress:**
https://github.com/leanprover-community/mathlib4/pull/37716 —
"feat(LinearAlgebra/Matrix/Determinant): Desnanot-Jacobi identity"
by slavanaprienko (opened 2026-04-06, status: awaiting-author).
Adds the identity to `Mathlib.LinearAlgebra.Matrix.Determinant.DesnanotJacobi`
using Bressoud's proof (adjugate-based, then lift to polynomial ring
to cancel `det(M)` factor). If merged, this eliminates the hard lemma
entirely — we just apply it through the matrix ring equivalence in
hex-matrix-mathlib.

**Exact division.** The division `/ a^{(k-1)}_{k-1,k-1}` in the
Bareiss recurrence is exact. This falls out of the invariant: both
sides of the Desnanot–Jacobi identity are integers, so the quotient
`a^{(k+1)}_{ij}` is an integer whenever the pivot is nonzero.
The computational side uses `Int.divExact`; the correctness proof
in hex-matrix-mathlib packages the divisibility witness from the
invariant.

**Zero-pivot handling: two-layer design.**

Note: "zero leading principal minor ⟹ det = 0" is **false**.
Example: `[[0,1],[1,0]]` has first principal minor 0 but det = -1.
A zero pivot means the no-pivot Bareiss precondition failed, not
that the matrix is singular.

Two-layer approach:

1. `bareissNoPivot` — the clean Bareiss recurrence without pivoting.
   Correctness proved under precondition `NonzeroBareissPivots M`
   (all leading principal minors nonzero). The bordered-minor
   invariant + Desnanot–Jacobi proof stays clean and simple.

2. `bareissDet` — the public API with row pivoting and sign
   tracking. Correct for all matrices. Proof: after pivoting, the
   reordered matrix has nonzero pivots, so apply
   `bareissNoPivot_eq_det` to the permuted matrix, then use
   `det_rowSwap` to account for the sign changes.

Pivoting infrastructure is shared with RREF (which already needs
row swaps). One verified pivot-search abstraction serves both.

**Where this lives.** Bareiss is implemented in hex-matrix
(computational). The `bareiss_eq_det` proof lives in
hex-matrix-mathlib (uses Desnanot–Jacobi, either from
mathlib4#37716 or proved locally using Mathlib's `Matrix.adjugate`).
The row-operation lemmas (`det_rowSwap`, `det_rowScale`,
`det_rowAdd`) are still needed in hex-matrix for RREF correctness
and are useful building blocks regardless.

---

### 8. Nullspace completeness

```lean
theorem nullspace_complete (E : IsEchelonForm M D) (v : Vector R m) :
    M * v = 0 → E.nullspace.toMatrix.spanContains v
```

**Why it's hard:** Must show the computed basis vectors (one per free
variable) span the entire kernel. The standard argument: any kernel
vector, when restricted to pivot columns, is determined by its free-
variable entries (back-substitution from RREF), so it's a linear
combination of the basis vectors. Formalizing the back-substitution
argument requires careful index manipulation.

---

## Tier 3: Hard but Well-Understood Patterns

### 11. Barrett reduction correctness

```lean
theorem BarrettCtx.toNat_mulMod (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat
```

Similar to Montgomery but simpler: compute q ≈ (a*b) / p using the
precomputed reciprocal, then r = a*b − q*p, with at most one
corrective subtraction. Still requires 128-bit intermediate reasoning.

---

### 12. Gauss's lemma

```lean
theorem content_mul (f g : ZPoly) :
    content (f * g) = content f * content g
```

Classical proof: assume f, g primitive, show f*g primitive by
contradiction — if prime p divides all coefficients of f*g, reduce
mod p and use the fact that F_p[x] has no zero divisors.

---

### 13. Ring equivalences (Mathlib bridges)

```lean
def equiv : DensePoly R ≃+* Polynomial R          -- hex-poly-mathlib
def equiv : GFq p n ≃+* GaloisField p n           -- hex-gfq-mathlib
def equiv : ZMod64 p ≃+* ZMod p                   -- hex-mod-arith-mathlib
```

These are "glue" theorems — define the map (coefficient-by-coefficient),
show it's bijective, show it preserves + and *. Tedious but mechanical.
Difficulty depends on how cooperative Mathlib's API is.

---

## Summary Table

| # | Theorem | Library | Blocking? |
|---|---------|---------|-----------|
| 1 | `prod_berlekampFactor` / `irreducible_of_mem_berlekampFactor` | hex-berlekamp | Yes (factoring) |
| 2 | `lll_short_vector` | hex-lll | Yes (poly-time BZ) |
| 3 | `lll_swap_bound` | hex-lll | Yes (termination) |
| 6 | Mignotte bound | hex-poly-z-mathlib | Yes (unconditional BZ) |
| 7 | `bareiss_eq_det` | hex-matrix | No (det not needed for BZ) |
| 8 | Nullspace completeness | hex-matrix | Yes (Berlekamp kernel) |
| 11 | Barrett correctness | hex-arith | Yes (performance) |
| 12 | Gauss's lemma | hex-poly-z | Yes (content machinery) |
| 13 | Ring equivalences | various -mathlib | No (bridges) |
