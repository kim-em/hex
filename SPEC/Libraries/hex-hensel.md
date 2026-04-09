# hex-hensel (Hensel lifting, depends on hex-poly-fp + hex-poly-z)

Lifts a factorization of `f mod p` to a factorization of `f mod p^k`.
Contains only the lifting algorithms — all correctness proofs live in
hex-hensel-mathlib.

**Contents:**
- **Linear Hensel lifting**: from `mod p^k` to `mod p^(k+1)`
- **Quadratic Hensel lifting**: from `mod p^k` to `mod p^(2k)` (doubling)
- **Multifactor lifting**: binary factor tree approach

Hex-hensel lifts to a requested precision `k`; the caller (typically
hex-berlekamp-zassenhaus) computes `k` from the Mignotte bound.

**Linear Hensel lifting algorithm:**

Input: `f, g, h : ZPoly` with `g` monic, `s, t : FpPoly p` with
`s*g + t*h ≡ 1 mod p`. Precondition (not checked): `g*h ≡ f mod p^k`.

```
1. e := coeffwise_div (f - g*h) p^k    -- truncating Int.div
2. (q, r) := divmod(t*e, g) in F_p[x]  -- deg(r) < deg(g)
3. g' := g + p^k * lift(r)
4. h' := h + p^k * lift(s*e + q*h mod p)
```

Correctness: `r*h + g*(s*e + q*h) = (s*g + t*h)*e = e mod p`, so
`g'*h' ≡ g*h + p^k*e ≡ f mod p^(k+1)`.

Key properties:
- `s, t` are computed once mod `p` and reused at every step
- `deg(δg) < deg(g)` from divmod, so `g'` stays monic of same degree
- `deg(δh) < deg(h)` follows from `deg(e) < deg(f) = deg(g) + deg(h)`
  (proof in hex-hensel-mathlib)
- Output coefficients are reduced mod `p^(k+1)`

**Quadratic Hensel lifting algorithm:**

Input: `f, g, h : ZPoly` with `g` monic, `s, t : ZPoly` with
`s*g + t*h ≡ 1 mod m`. Precondition: `g*h ≡ f mod m`.

Factor update (mod `m²`):
```
1. e := f - g*h
2. (q, r) := divmod(t*e, g) in (Z/m²Z)[x]
3. g* := g + r mod m²
4. h* := h + s*e + q*h mod m²
```

Bezout update — divmod by `g*` (which is monic):
```
5. b := s*g* + t*h* - 1
6. (q, r) := divmod(t*b, g*) in (Z/m²Z)[x]
7. t* := t - r
8. s* := s - s*b - q*h*
```

Correctness: `s**g* + t**h* = 1 - b²`. Since `b ≡ 0 mod m`, we get
`b² ≡ 0 mod m²`, so `s**g* + t**h* ≡ 1 mod m²`.

Note: divmod by `g*` (not `h*`) because `g*` is monic; `h` may not be.
Both factor and Bezout coefficients must be lifted together at each
doubling step (unlike linear lifting which reuses `s, t` mod `p`).

**Strategy**: Start with linear lifting (simpler invariant, easier to
verify). Add quadratic as an optimization proved equivalent via
uniqueness (in hex-hensel-mathlib).
