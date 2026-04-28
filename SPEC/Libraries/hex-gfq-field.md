# hex-gfq-field (GF(q) as a field, depends on hex-gfq-ring)

Field structure on top of the canonical quotient-ring implementation
from hex-gfq-ring. Takes any irreducible polynomial as parameter — not
tied to Conway polynomials.

The key layering decision is that this library does not introduce a
separate representation. `FiniteField p f hf hirr` should be a thin
wrapper over `PolyQuotient p f hf`, or reuse that same underlying data
with stronger assumptions. There is one quotient representation, one
canonical reduction function, and one equality story across the ring and
field libraries.

**Contents:**
- `FiniteField p f hf hirr` — the field `F_p[x]/(f)`, where `hf : 0 <
  f.degree` and `hirr : Irreducible f`
- Coercions or conversion functions to and from `PolyQuotient p f hf`
- Multiplicative inverse via extended GCD in `F_p[x]`
- Division and exponentiation. `pow x n` is square-and-multiply
  (`O(log n)` field multiplications); the textbook `n+1 ↦ pow n * x`
  recursion is forbidden because cryptographic exponents (e.g. `n =
  p` for Frobenius, with `p ≈ 2^31`) make linear-time `pow`
  non-terminating.
- Frobenius map `frob : FiniteField p f hf hirr → FiniteField p f hf hirr`,
  computed as `pow x p` (and therefore inheriting the
  square-and-multiply complexity)
- `Lean.Grind.Field (FiniteField p f hf hirr)` instance
- `IsCharP (FiniteField p f hf hirr) p`

The irreducibility proof `hirr` may come from hex-berlekamp (either via
the algorithm or via a certificate), but this library should not depend
on hex-berlekamp for its core API. It works for any supplied proof of
irreducibility. For a canonical choice of irreducible modulus, see
hex-gfq.

`Fintype` and cardinality belong in the Mathlib bridge, not here. The
computational library should expose the concrete field operations and
their algebraic laws, while `hex-gfq-mathlib` supplies finiteness,
cardinality, and correspondence with Mathlib's abstract finite fields.

**Key properties:**
- `inv a * a = 1` for `a ≠ 0`
- `a / b = a * b⁻¹`
- `frob(a) = a ^ p`
- Field axioms for `FiniteField p f hf hirr`
