# Proof Triage

Scratch space for researching proof strategies. Once a proof is
understood and vetted, it gets incorporated into PLAN.md (under the
relevant library section) and deleted from here.

---

## Tier 1: Major Theorems

### 6. Mignotte bound validity

**Corrected statement** (needs `hf : f ≠ 0`; false otherwise since
every polynomial divides 0):

```lean
-- In hex-poly-z-mathlib
-- The core theorem is over ℝ (matching Mathlib's Mahler measure API)
theorem mignotte_bound (f g : Polynomial ℤ) (hf : f ≠ 0) (hg : g ∣ f) (j : ℕ) :
    (Int.natAbs (g.coeff j) : ℝ) ≤ Nat.choose g.natDegree j * l2norm f
```

where `l2norm f := Real.sqrt (∑ i in f.support, (f.coeff i : ℝ) ^ 2)`.
An integer-facing corollary can extract `|g.coeff j| ≤ ⌊...⌋₊` if
needed by downstream code.

**Mathlib API.**
https://github.com/leanprover-community/mathlib4/pull/37349 added:

- `mahlerMeasure_le_sqrt_sum_sq_norm_coeff` (Landau's inequality)
- `le_mahlerMeasure_mul_right` (monotonicity)
- `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`
  (Mignotte bound)

The Mahler measure library (`Mathlib.Analysis.Polynomial.MahlerMeasure`)
provides:

- `mahlerMeasure_mul`: `M(p * q) = M(p) * M(q)`
- `norm_coeff_le_choose_mul_mahlerMeasure`: `‖p.coeff n‖ ≤ C(deg, n) * M(p)`
- `one_le_prod_max_one_norm_roots`: `∏ max(1, ‖αᵢ‖) ≥ 1`

**Proof outline and glue steps.**

1. **Cast to `ℂ[X]`.** Define `F G H : Polynomial ℂ` via
   `Polynomial.map (Int.castRingHom ℂ)`. From `hg`, obtain
   `h : Polynomial ℤ` with `f = g * h`; map to `F = G * H`
   via `Polynomial.map_mul`.

2. **Nonzero cofactor.** From `hf` and `f = g * h`, since
   `Polynomial ℤ` is a domain, get `h ≠ 0`. Then `H ≠ 0` by
   injectivity of `Int.castRingHom ℂ` (via `Polynomial.map_ne_zero_of_injective`
   or `map_injective`). This gives `1 ≤ H.mahlerMeasure`.

3. **Monotonicity.** Apply `le_mahlerMeasure_mul_right` (or use
   `mahlerMeasure_mul` + `1 ≤ H.mahlerMeasure`) to get
   `G.mahlerMeasure ≤ F.mahlerMeasure`.

4. **Coefficient bound.** Apply
   `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`
   to `G` (with `1 ≤ G.mahlerMeasure` from integer polynomial
   nonzero, or chain through `F`'s bound directly):
   `‖G.coeff j‖ ≤ C(G.natDegree, j) * F.mahlerMeasure`.

5. **Landau bound.** Apply `mahlerMeasure_le_sqrt_sum_sq_norm_coeff`
   to bound `F.mahlerMeasure ≤ √(∑ ‖F.coeff i‖²)`.

6. **Transport back to `ℤ`.** Three small lemmas:
   - **Coefficients:** `G.coeff j = ↑(g.coeff j)` — by
     `Polynomial.coeff_map`.
   - **Degree:** `G.natDegree = g.natDegree` — by
     `Polynomial.natDegree_map_of_injective` (injective cast).
   - **Norms:** `‖((g.coeff j : ℤ) : ℂ)‖ = |(g.coeff j : ℝ)|` —
     via `Complex.norm_intCast` or `Complex.norm_ofReal` +
     `Int.cast_abs`. Similarly the L2 sum over `F`'s coefficients
     equals `l2norm f` since `‖((f.coeff i : ℤ) : ℂ)‖² = (f.coeff i : ℝ)²`.

**Other open Mathlib PR:** https://github.com/leanprover-community/mathlib4/pull/33463
(Mahler Measure for other rings) would simplify the `ℤ → ℂ` coercion
further by providing Mahler measure directly on `ℤ[X]`.

---

## Summary Table

| # | Theorem | Library | Blocking? |
|---|---------|---------|-----------|
| 1 | `prod_berlekampFactor` / `irreducible_of_mem_berlekampFactor` | hex-berlekamp | Yes (factoring) |
| 2 | `lll_short_vector` | hex-lll | Yes (poly-time BZ) |
| 3 | `lll_swap_bound` | hex-lll | Yes (termination) |
| 6 | Mignotte bound | hex-poly-z-mathlib | Yes (unconditional BZ) |
