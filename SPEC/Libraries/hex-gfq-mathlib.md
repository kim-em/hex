# hex-gfq-mathlib (depends on hex-gfq + Mathlib)

Proves `GFq p n ≃+* GaloisField p n` (Mathlib's Galois field).
Proof strategy: apply `FiniteField.ringEquivOfCardEq` from Mathlib,
which just needs `Fintype.card (GFq p n) = Fintype.card (GaloisField p n)`.
Both sides equal `p ^ n` — Mathlib has `GaloisField.card` and we need
`card_finiteField` from hex-gfq-field.
