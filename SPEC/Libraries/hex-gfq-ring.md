# hex-gfq-ring (GF(q) as a ring, depends on hex-poly-fp)

Quotient ring `F_p[x] / (f)` for an arbitrary polynomial `f` over `F_p`.

**Contents:**
- `PolyQuotient p f` — elements of `F_p[x] / (f)`, represented as
  polynomials of degree < deg(f)
- Ring operations: addition, multiplication (multiply then reduce mod f),
  negation
- `Lean.Grind.CommRing` instance

This does NOT require `f` to be irreducible — the quotient is always a
ring. When `f` is irreducible, the quotient is a field, but that's
hex-gfq-field's job.

**Key properties:**
- Ring axioms
- `reduce (a * b) = reduce a * reduce b` (well-definedness of quotient)
- Canonical representative: degree < deg(f)
