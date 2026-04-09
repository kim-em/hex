# hex-poly-mathlib (depends on hex-poly + Mathlib)

Proves the ring equivalence between `DensePoly R` and Mathlib's
`Polynomial R`:

```lean
def equiv [CommRing R] [DecidableEq R] : DensePoly R ≃+* Polynomial R
```

Also proves GCD/ExtGCD correspondence with Mathlib's `Polynomial.gcd`.
