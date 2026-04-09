# hex-gfq (convenience wrapper, depends on hex-gfq-field + hex-conway)

Thin wrapper providing `GFq p n` — the canonical finite field with
`p^n` elements, using the Conway polynomial as the irreducible modulus.

```lean
def GFq (p n : Nat) := FiniteField p (conwayPoly p n) (conwayPoly_irreducible p n)
```

The user writes `GFq 2 8` and gets `GF(2^8)` with no further choices.
For non-Conway models (e.g. AES's `x^8 + x^4 + x^3 + x + 1`), use
`FiniteField` directly from hex-gfq-field.
