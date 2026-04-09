# hex-poly (dense polynomial library, no dependencies)

The core polynomial library.

**Dense representation:**
```lean
structure DensePoly (R : Type*) [Zero R] [DecidableEq R] where
  coeffs : Array R
  normalized : coeffs.size = 0 ∨ coeffs.back! ≠ 0
```

The normalization invariant (no trailing zeros) ensures structural equality
= semantic equality. Every operation maintains this invariant.

- Index = degree, `coeffs[i]` is coefficient of `x^i`
- Normalization invariant: no trailing zeros
- Structural equality = semantic equality
- O(1) degree, O(1) coefficient access

**Operations:**
- Addition, subtraction, multiplication (schoolbook, Karatsuba for large degree)
- Division with remainder (for monic divisors; general division over fields)
- Polynomial GCD (Euclidean algorithm)
- Extended GCD (Bezout coefficients: `a*f + b*g = gcd(f,g)`)
- Evaluation (Horner's method)
- Composition, derivative
- Content and primitive part (for `DensePoly Int`)

**Polynomial GCD — key properties:**
- `gcd f g` divides both `f` and `g`
- Every common divisor of `f` and `g` divides `gcd f g`
- Bezout: `∃ a b, a * f + b * g = gcd f g`

**Existential CRT for polynomials** (corollary of Bezout):

```lean
def polyCRT [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R) : DensePoly R :=
  u * t * b + v * s * a

theorem polyCRT_mod_fst [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R)
    (hbez : s * a + t * b = 1) :
    (polyCRT a b u v s t) % a = u % a

theorem polyCRT_mod_snd [CommRing R] [DecidableEq R]
    (a b u v s t : DensePoly R)
    (hbez : s * a + t * b = 1) :
    (polyCRT a b u v s t) % b = v % b
```

Given coprime `a, b` with Bezout coefficients `s, t`, constructs `h`
with `h ≡ u (mod a)` and `h ≡ v (mod b)`. Used by hex-hensel,
hex-gfq-ring, and hex-berlekamp-mathlib (Berlekamp correctness proof).
