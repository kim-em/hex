# hex-berlekamp (factoring over F_p, depends on hex-poly-fp + hex-matrix + hex-gfq-ring)

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
structure IrreducibilityCertificate where
  p : Nat
  n : Nat
  -- Square-and-multiply witnesses for X^(p^k) mod f
  powChain : Array (FpPoly p)
  -- Bezout coefficients for coprimality at each maximal divisor
  bezout : Array (FpPoly p × FpPoly p)
```

The prime `p` and target degree `n` are bundled as fields so that a
certificate is self-describing and collections of certificates at
different primes can share a single type. `FpPoly p` references use
the preceding field, which Lean 4 supports natively.

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
