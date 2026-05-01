# hex-hensel (Hensel lifting, depends on hex-poly-fp + hex-poly-z)

Lifts a factorization of `f mod p` to a factorization of `f mod p^k`.
This library contains the lifting algorithms together with the
computational invariant lemmas needed by downstream code. The heavier
abstract-algebraic correctness and transfer results live in
hex-hensel-mathlib.

The computational functions in this library are **total**. They return
plain data, not sigma-types carrying proof obligations. Monicity,
congruence modulo `p^k`, and Bezout identities are treated as algorithm
preconditions, not as bundled proof fields in the computational data
structures. Theorems in this library record how those invariants evolve
under the computation.

Congruence modulo an integer modulus is the shared notion from
`hex-poly-z`, not a Hensel-specific predicate:
`ZPoly.congr f g m`. This is the relation used throughout the API for
statements like "mod `p^k`" and "mod `p^(k+1)`".

**Contents:**
- **Bridge operations** between `ZPoly` and `FpPoly p`:
  ```lean
  def ZPoly.modP (p : Nat) : ZPoly → FpPoly p
  def FpPoly.liftToZ (f : FpPoly p) : ZPoly
  def ZPoly.reduceModPow (f : ZPoly) (p k : Nat) : ZPoly
  ```
- Canonicalization convention for bridge operations:
  - `FpPoly.liftToZ` uses the standard nonnegative representatives for
    coefficients, i.e. each lifted coefficient lies in `[0, p)`.
  - `ZPoly.reduceModPow f p k` reduces each coefficient to the standard
    representative in `[0, p^k)`, then renormalizes the resulting
    `ZPoly` to remove trailing zero coefficients.
- **Linear Hensel lifting**: from `mod p^k` to `mod p^(k+1)`
- **Quadratic Hensel lifting**: from `mod p^k` to `mod p^(2k)` (doubling)
- **Multifactor lifting**: public API returns a list/array of lifted
  factors; any binary factor tree is internal to the implementation

Suggested computational result types:
```lean
structure LinearLiftResult where
  g : ZPoly
  h : ZPoly

structure QuadraticLiftResult where
  g : ZPoly
  h : ZPoly
  s : ZPoly
  t : ZPoly
```

Hex-hensel lifts to a requested precision `k`; the caller (typically
hex-berlekamp-zassenhaus) computes `k` from the Mignotte bound. The
public meaning of "lift to precision `k`" is always "produce data valid
modulo `p^k`".

Suggested top-level entry points:
```lean
def linearHenselStep
    (p k : Nat) (f g h : ZPoly) (s t : FpPoly p) : LinearLiftResult

def quadraticHenselStep
    (m : Nat) (f g h s t : ZPoly) : QuadraticLiftResult

def henselLift
    (p k : Nat) (f g h : ZPoly) (s t : FpPoly p) : LinearLiftResult

def multifactorLift
    (p k : Nat) (f : ZPoly) (factors : Array ZPoly) : Array ZPoly
```

For the multifactor API, the public product convention is the left fold
of multiplication with identity `1`:
```lean
def Array.polyProduct (factors : Array ZPoly) : ZPoly :=
  factors.foldl (· * ·) 1
```
This fixes the exact meaning of statements such as "the product of the
lifted factors is congruent to `f` mod `p^k`". The public contract does
not treat factor order as semantically significant beyond this ordered
array interface.

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
  (proved in hex-hensel as a computational invariant)
- Output coefficients are reduced mod `p^(k+1)`
- Companion theorem shape (in `hex-hensel`):
  ```lean
  theorem linearHenselStep_spec
      (hprod : ZPoly.congr (g * h) f (p^k))
      (hbez : ... ) (hmonic : ...)
      : let r := linearHenselStep p k f g h s t
        ZPoly.congr (r.g * r.h) f (p^(k+1))
  ```

Further computational lemmas in `hex-hensel` should include bridge and
congruence facts needed by downstream code, such as:
- `ZPoly.modP`, `FpPoly.liftToZ`, and `ZPoly.reduceModPow` compatibility lemmas
- congruence preservation under `+`, `*`, and coefficient-wise reduction
- monicity/degree preservation lemmas needed by iterative lifting and
  by `hex-berlekamp-zassenhaus`

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

Suggested companion theorem shape (in `hex-hensel`):
```lean
theorem quadraticHenselStep_spec
    (hprod : ZPoly.congr (g * h) f m)
    (hbez : ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : ...)
    : let r := quadraticHenselStep m f g h s t
      ZPoly.congr (r.g * r.h) f (m*m) ∧
      ZPoly.congr (r.s * r.g + r.t * r.h) 1 (m*m)
```

**Multifactor lifting API:**

The public multifactor interface should be list-shaped, because the
downstream factoring pipeline wants a collection of lifted factors, not
an implementation-specific factor tree. The implementation may still use
a binary factor tree internally for efficiency and for divide-and-conquer
proofs, but that tree is not part of the external contract.

Suggested companion theorem shape (in `hex-hensel`):
```lean
theorem multifactorLift_spec
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hinv : MultifactorLiftInvariant p k f factors.toList)
    : ZPoly.congr (Array.polyProduct (multifactorLift p k f factors)) f (p^k)
```
The invariant is recursive over the sequential split tree. Each nontrivial
split carries the same start invariant, degree preservation hypothesis, and
Bezout preservation hypothesis required by `henselLift_spec`; the tail carries
the invariant for the lifted complementary factor. Product congruence modulo
`p` alone is not sufficient for multifactor lifting.

Theorems that belong in `hex-hensel-mathlib` are the ones that use
Mathlib's abstract polynomial/divisibility/coprimality infrastructure
rather than just the computational `ZPoly`/`FpPoly` representations.
Examples include uniqueness of lifts, `coprime_mod_p_lifts`, and
transfer theorems phrased in terms of Mathlib polynomials.

**Strategy**: Start with linear lifting (simpler invariant, easier to
verify). Add quadratic as an optimization proved equivalent via
uniqueness (in hex-hensel-mathlib).
