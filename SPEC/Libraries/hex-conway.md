# hex-conway (Conway polynomial database, depends on hex-berlekamp)

Conway polynomials are canonical irreducible polynomials `C(p, n)` for
each prime `p` and degree `n`, satisfying compatibility conditions
across degree divisors: if `m | n`, then the image of a root of
`C(p, n)` under the norm map `GF(p^n) → GF(p^m)` is a root of
`C(p, m)`. This ensures that embeddings `GF(p^m) ↪ GF(p^n)` are
coherent.

**Two sources of Conway polynomials:**

1. **Hardcoded database** — commonly used `(p, n)` pairs, sourced from
   Frank Lübeck's tables. Each entry comes with a Lean-checked
   irreducibility certificate (from hex-berlekamp) and a proof of
   compatibility with all divisor-degree entries already in the database.

2. **On-demand computation** — for `(p, n)` pairs not in the database,
   search for the lexicographically smallest monic irreducible polynomial
   of degree `n` over `F_p` satisfying the compatibility condition with
   all `C(p, m)` for `m | n`. This uses hex-berlekamp for irreducibility
   testing. The result is deterministic (the definition of Conway
   polynomial specifies "lexicographically smallest").

**API:**
```lean
def conwayPoly (p n : Nat) : FpPoly p

theorem conwayPoly_irreducible (p n : Nat) : Irreducible (conwayPoly p n)
theorem conwayPoly_compat (p m n : Nat) (h : m ∣ n) : ...
```

`conwayPoly` always returns a result (falling back to on-demand
computation). For small `(p, n)` it hits the hardcoded table; for
larger values it computes. The caller doesn't need to know which path
was taken.

**hex-gfq** then defines `GFq p n := FiniteField p (conwayPoly p n)
(conwayPoly_irreducible p n)`. When a user asks for `GF(p^n)`, the
Conway polynomial is chosen automatically.
