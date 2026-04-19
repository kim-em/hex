# hex-gfq (convenience wrapper, depends on hex-gfq-field + hex-conway + hex-gf2)

User-facing constructors for canonical finite fields. This is the layer
where the library chooses the irreducible polynomial for you.

For all primes `p`, `GFq p n` uses the same generic quotient-field
construction from `hex-gfq-field`, instantiated with the Conway
polynomial from `hex-conway`. For `p = 2`, this library additionally
provides an optimized convenience constructor built on `hex-gf2`.

```lean
/-- Canonical finite field with `p^n` elements, always using the generic
    quotient-field representation from `hex-gfq-field`. In particular,
    `GFq 2 n` does NOT switch to the packed `hex-gf2` representation. -/
def GFq (p n : Nat) :=
  FiniteField p (conwayPoly p n) (conwayPoly_nonconstant p n)
    (conwayPoly_irreducible p n)

/-- Optimized canonical GF(2^n), using the Conway polynomial chosen by
    `hex-conway` but represented with the packed `hex-gf2` backend. -/
def GF2q (n : Nat) := ...

/-- The optimized `p = 2` constructor is mathematically the same field
    as the generic canonical constructor. -/
def GF2q.equivGFq (n : Nat) : GF2q n ≃+* GFq 2 n := ...
```

API intent:

- `GFq p n` is the canonical, always-available constructor, with a
  uniform generic representation for every `p`.
- `GF2q n` is the specialized `p = 2` constructor using the optimized
  representation from `hex-gf2`.
- `GF2q n ≃+* GFq 2 n`, so users can move between the optimized and
  generic `p = 2` models without changing the mathematics.
- Both constructors choose the modulus automatically via Conway
  polynomials, so the user supplies neither a polynomial nor an
  irreducibility proof.

The user writes `GFq 3 5` and gets the canonical `GF(3^5)`. The user
writes `GF2q 8` and gets the optimized canonical `GF(2^8)` backed by
packed bitwise arithmetic. For non-Conway models (e.g. AES's
`x^8 + x^4 + x^3 + x + 1`), use `FiniteField` directly from
hex-gfq-field or `GF2n`/`GF2nPoly` directly from hex-gf2.
