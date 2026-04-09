# hex-poly-z-mathlib (depends on hex-poly-z + Mathlib)

Proves `DensePoly Int ≃+* Polynomial ℤ` and the Mignotte bound.

**Mignotte bound — proof strategy.**

Statement (needs `hf : f ≠ 0`; false otherwise since every polynomial
divides 0):

```lean
theorem mignotte_bound (f g : Polynomial ℤ) (hf : f ≠ 0) (hg : g ∣ f) (j : ℕ) :
    (Int.natAbs (g.coeff j) : ℝ) ≤ Nat.choose g.natDegree j * l2norm f
```

where `l2norm f := Real.sqrt (∑ i in f.support, (f.coeff i : ℝ) ^ 2)`.
The core theorem is over `ℝ` (matching Mathlib's Mahler measure API).
An integer-facing corollary can extract `|g.coeff j| ≤ ⌊...⌋₊` if
needed by downstream code.

**Mathlib API.** All heavy analysis is in
`Mathlib.Analysis.Polynomial.MahlerMeasure`.
https://github.com/leanprover-community/mathlib4/pull/37349 added:

- `mahlerMeasure_le_sqrt_sum_sq_norm_coeff` (Landau's inequality)
- `le_mahlerMeasure_mul_right` (monotonicity)
- `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`
  (Mignotte bound)

The earlier Mahler measure library (by Fabrizio Barroero) provides:

- `mahlerMeasure_mul`: `M(p * q) = M(p) * M(q)`
- `norm_coeff_le_choose_mul_mahlerMeasure`: `‖p.coeff n‖ ≤ C(deg, n) * M(p)`
- `one_le_prod_max_one_norm_roots`: `∏ max(1, ‖αᵢ‖) ≥ 1`

**Proof outline and glue steps.**

1. **Cast to `ℂ[X]`.** Define `F G H : Polynomial ℂ` via
   `Polynomial.map (Int.castRingHom ℂ)`. From `hg`, obtain
   `h : Polynomial ℤ` with `f = g * h`; map to `F = G * H`
   via `Polynomial.map_mul`.

2. **Nonzero factors.** From `hf` and `f = g * h`, since
   `Polynomial ℤ` is a domain, get `g ≠ 0` and `h ≠ 0`. Then
   `H ≠ 0` (and `G ≠ 0`) by injectivity of `Int.castRingHom ℂ`
   (via `Polynomial.map_ne_zero_of_injective` or `map_injective`).

3. **Mahler measure ≥ 1 for integer polynomials.** `H ≠ 0` alone
   is not enough (`(1/2 : ℂ[X])` has Mahler measure `1/2`). The
   key is that `h` has integer coefficients: `leadingCoeff h` is
   a nonzero integer, so `‖leadingCoeff H‖ ≥ 1`. Combined with
   `one_le_prod_max_one_norm_roots` and
   `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`, this gives
   `1 ≤ H.mahlerMeasure`.

4. **Monotonicity.** Apply `le_mahlerMeasure_mul_right` (or use
   `mahlerMeasure_mul` + `1 ≤ H.mahlerMeasure`) to get
   `G.mahlerMeasure ≤ F.mahlerMeasure`.

5. **Coefficient bound.** Apply
   `norm_coeff_le_choose_mul_mahlerMeasure` to `G`:
   `‖G.coeff j‖ ≤ C(G.natDegree, j) * G.mahlerMeasure`.
   Chain with step 4 to get `≤ C(G.natDegree, j) * F.mahlerMeasure`.

6. **Landau bound.** Apply `mahlerMeasure_le_sqrt_sum_sq_norm_coeff`
   to bound `F.mahlerMeasure ≤ √(∑ ‖F.coeff i‖²)`.

7. **Transport back to `ℤ`.** Four lemmas:
   - **Coefficients:** `G.coeff j = ↑(g.coeff j)` — by
     `Polynomial.coeff_map`.
   - **Degree:** `G.natDegree = g.natDegree` — by
     `Polynomial.natDegree_map_of_injective` (injective cast).
   - **Support:** `F.support = f.support` — by
     `Polynomial.support_map_of_injective` (injective cast).
     Needed to rewrite the L2 sum from `F`'s support to `f`'s.
   - **Norms:** `‖((g.coeff j : ℤ) : ℂ)‖ = |(g.coeff j : ℝ)|` —
     via `Complex.norm_intCast` or `Complex.norm_ofReal` +
     `Int.cast_abs`. The L2 sum rewrites similarly since
     `‖((f.coeff i : ℤ) : ℂ)‖² = (f.coeff i : ℝ)²`. The final
     LHS rewrites from `‖...‖` to `(Int.natAbs (g.coeff j) : ℝ)`
     to match the theorem statement.

**Open Mathlib PR:** https://github.com/leanprover-community/mathlib4/pull/33463
("Mahler Measure for other rings") extends the Mahler measure definition
beyond `ℂ[X]`. If this lands, the `ℤ → ℂ` coercion step becomes cleaner.
