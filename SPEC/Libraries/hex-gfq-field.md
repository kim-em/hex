# hex-gfq-field (GF(q) as a field, depends on hex-berlekamp)

Extends `hex-gfq-ring` with field operations when the modulus is
irreducible. Takes any irreducible polynomial as parameter — not tied
to Conway polynomials.

**Contents:**
- `FiniteField p f (hirr : Irreducible f)` — the field `F_p[x]/(f)`,
  where `f` is any irreducible polynomial over `F_p`
- Multiplicative inverse via extended GCD in `F_p[x]`
- `Lean.Grind.Field` instance
- `IsCharP (FiniteField p f hirr) p`

The irreducibility proof `hirr` comes from hex-berlekamp (either via
the algorithm or via a certificate). This type is not tied to Conway
polynomials — any irreducible polynomial works (e.g. AES uses
`x^8 + x^4 + x^3 + x + 1` over `F_2`). For a canonical choice, see
hex-gfq.

**Key properties:**
- `inv a * a = 1` for `a ≠ 0`
- `Fintype (FiniteField p f hirr)` with `card = p ^ f.degree`
- Frobenius automorphism: `frob(a) = a^p`
