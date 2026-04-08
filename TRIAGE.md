# Proof Triage

Scratch space for researching proof strategies. Once a proof is
understood and vetted, it gets incorporated into PLAN.md (under the
relevant library section) and deleted from here.

---

## Tier 1: Major Theorems

### 4. Rabin's irreducibility test (`rabin_irreducible`)

```lean
theorem rabin_irreducible (f : FpPoly p) (hf : f.degree = n) :
    rabinTest f = true ↔ Irreducible f
```

Unlike Berlekamp's completeness proof (which avoids finite field
theory entirely), both directions of Rabin's theorem require the
theory of finite field extensions.

**(→) test passes ⟹ irreducible.** Contrapositive: if `f` is
reducible, `f = g * h` with `g` irreducible of degree `d < n`.
Then `d | n` (subfield containment), so `d ≤ n/q` for some prime
`q | n`, giving `g | X^(p^(n/q)) - X` and thus
`gcd(f, X^(p^(n/q)) - X) ≠ 1`.

**(←) irreducible ⟹ test passes.** Two parts:
- `f | X^(p^n) - X`: in `F_p[x]/(f)` (a field with `p^n` elements),
  every element satisfies `a^(p^n) = a` by Lagrange's theorem on the
  multiplicative group. So `f | X^(p^n) - X`.
- `gcd(f, X^(p^(n/q)) - X) = 1`: if nontrivial, `f` would share a
  root with `X^(p^(n/q)) - X`, placing it in `GF(p^(n/q))`. But
  the minimal polynomial of a root of `f` has degree `n`, and
  `n/q < n` — contradiction.

**Finite field theory needed** (not needed for Berlekamp):
1. Irreducible `f` of degree `n` ⟹ `F_p[x]/(f)` is a field
   (quotient by irreducible is integral domain, finite integral
   domain is a field)
2. `|F_p[x]/(f)| = p^n` (counting polynomials of degree `< n`)
3. `a^(p^n) = a` for all `a ∈ GF(p^n)` (Lagrange on the
   multiplicative group of order `p^n - 1`)
4. `GF(p^m) ⊆ GF(p^n)` iff `m | n`
5. If `g` is irreducible of degree `d` and `g | X^(p^n) - X`,
   then `d | n`

**Where this lives.** Rabin's test is implemented in `hex-berlekamp`
(computational black box). Both directions of the correctness proof
live in `hex-berlekamp-mathlib`, where Mathlib provides all the
finite field theory (steps 1-5 above).

---

### 5. Hensel uniqueness (`hensel_unique`)

```lean
theorem hensel_unique (f g h g' h' : ZPoly) (p k : Nat) :
    g.leadingCoeff = 1 →
    g * h ≡ f [MOD p^k] → g' * h' ≡ f [MOD p^k] →
    g ≡ g' [MOD p] → h ≡ h' [MOD p] →
    coprime_mod g h p →
    g = g' ∧ h = h'
```

**Why it's hard:** Induction on k. The base case (k=1) is immediate.
The inductive step requires showing that the coprimality condition
lifts: if g, h are coprime mod p and g*h ≡ f mod p^k, then the
Bezout coefficients can be adjusted to work mod p^(k+1). The
leading coefficient condition (g monic) pins down the factorization
uniquely — without it, you can redistribute units between g and h.

The plan labels this "the deep theorem." It's the key ingredient for
connecting linear and quadratic Hensel lifting (they produce the same
result, so quadratic is a valid optimization).

**Research needed:**
- Exact statement of the coprimality lifting lemma
- Whether the induction is on k or on the precision doubling steps
- The Isabelle proof structure for this

---

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

**Why it's hard:** Must track the determinant through fraction-free
Gaussian elimination. Each Bareiss step performs the recurrence
a_{ij}^{(k)} = (a_{kk} · a_{ij} − a_{ik} · a_{kj}) / a_{k−1,k−1}
where the division is exact. The proof shows this equals applying row
operations (which have known determinant effects) and then dividing
by the previous pivot — the key being that the division is always
exact (Sylvester's identity or direct induction).

**Research needed:**
- Whether to use the row-operation approach or the Sylvester identity
  approach (the plan mentions both)
- Sylvester's identity is listed as "further work" — is it needed for
  the primary proof?

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

### 9. Montgomery correctness (`toNat_mulMont`)

```lean
theorem MontCtx.toNat_mulMont (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat
```

**Why it's hard:** Montgomery reduction computes (T + (T · p' mod R) · p) / R
where R = 2^64. The proof requires: (1) the result is congruent to
T · R⁻¹ mod p, (2) it's in range [0, 2p), (3) a conditional
subtraction brings it into [0, p). All of this at the UInt64 / 2^64
level, where overflow semantics must be handled precisely. Lean's
`UInt64` arithmetic wraps mod 2^64, so every intermediate step needs
careful bounds tracking.

The Montgomery inverse p' satisfying p' · p ≡ −1 (mod 2^64) must
also be computed and verified (via Newton's method on UInt64, or
extended GCD).

**Research needed:**
- Lean 4's current `UInt64` lemma library — what's available for
  overflow reasoning?
- Whether to prove at the `Nat` level and cast down, or work directly
  with `UInt64`

---

### 10. Factor uniqueness up to associates (`factor_unique`)

```lean
theorem factor_unique (f : ZPoly) (gs hs : List ZPoly) :
    gs.prod = f → hs.prod = f →
    (∀ g ∈ gs, Irreducible g) → (∀ h ∈ hs, Irreducible h) →
    gs ~ hs  -- multiset equality up to associates
```

**Why it's hard:** This is unique factorization in Z[x]. Requires
Gauss's lemma (product of primitive polynomials is primitive) plus
unique factorization in F_p[x] (which follows from F_p[x] being a
Euclidean domain). The full proof chains: Z[x] is a UFD because Z
is a UFD and the polynomial ring over a UFD is a UFD (via Gauss).

**Research needed:**
- Whether to prove UFD for Z[x] directly or factor through a more
  general result
- The Isabelle approach to this

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
| 4 | `rabin_irreducible` | hex-berlekamp | No (Berlekamp suffices) |
| 5 | `hensel_unique` | hex-hensel | Yes (quadratic lift) |
| 6 | Mignotte bound | hex-poly-z-mathlib | Yes (unconditional BZ) |
| 7 | `bareiss_eq_det` | hex-matrix | No (det not needed for BZ) |
| 8 | Nullspace completeness | hex-matrix | Yes (Berlekamp kernel) |
| 9 | Montgomery correctness | hex-arith | Yes (performance) |
| 10 | `factor_unique` | hex-bz-mathlib | No (correctness suffices) |
| 11 | Barrett correctness | hex-arith | Yes (performance) |
| 12 | Gauss's lemma | hex-poly-z | Yes (content machinery) |
| 13 | Ring equivalences | various -mathlib | No (bridges) |
