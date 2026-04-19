# hex-gfq-ring (GF(q) as a ring, depends on hex-poly-fp)

Canonical quotient-ring implementation for `F_p[x] / (f)`.

We only form quotient rings by a nonconstant modulus. Concretely, the
public quotient type should carry a hypothesis `0 < f.degree`, so the
canonical-representative invariant "degree < deg(f)" is meaningful and
we do not need to special-case `f = 0` or constant moduli throughout the
API.

**Contents:**
- `reduceMod (f : FpPoly p) : FpPoly p → FpPoly p` — canonical remainder
  on division by `f`
- `PolyQuotient p f hf` — quotient elements, represented by a reduced
  polynomial modulo `f`
- Smart constructor `ofPoly : FpPoly p → PolyQuotient p f hf`
- Projection `repr : PolyQuotient p f hf → FpPoly p`
- Ring operations: addition, multiplication, negation, subtraction,
  exponentiation; every operation reduces via `reduceMod`
- `Lean.Grind.CommRing (PolyQuotient p f hf)` instance

Representation choice: the stored representative is always canonical.
Callers do not manage reduction manually; `ofPoly` and all ring
operations normalize through `reduceMod`. Equality of quotient elements
is therefore equality of canonical representatives, not a separate
setoid-style relation.

This does NOT require `f` to be irreducible — the quotient is always a
ring. When `f` is irreducible, the same underlying representation
supports a field structure; that extension belongs to hex-gfq-field.

**Key properties:**
- `repr (ofPoly a) = reduceMod f a`
- `degree (repr x) < degree f`
- `ofPoly (reduceMod f a) = ofPoly a`
- `reduceMod f (a + b) = reduceMod f (reduceMod f a + reduceMod f b)`
- `reduceMod f (a * b) = reduceMod f (reduceMod f a * reduceMod f b)`
- Ring axioms for `PolyQuotient p f hf`
