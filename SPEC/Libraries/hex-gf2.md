# hex-gf2 (GF(2) packed arithmetic, depends on hex-poly)

Packed bitwise representation of polynomials over F_2. Addition is
XOR, multiplication uses carry-less multiply. Substantially faster
than the generic `FpPoly 2` path (up to 64x for addition-heavy
workloads). Actual speedups depend on workload; benchmarks comparing
`GF2Poly` vs `FpPoly 2` for Berlekamp matrix construction and
polynomial GCD are planned.

**Contents:**

```lean
/-- Polynomial over F_2, packed into 64-bit words.
    Bit j of words[i] represents the coefficient of x^(64*i + j). -/
structure GF2Poly where
  words : Array UInt64
  degree : Nat
  wf : (words = #[] ∧ degree = 0) ∨
       (words.back! ≠ 0 ∧ degree < 64 * words.size ∧
        words[degree / 64]! &&& (1 <<< (degree % 64)) ≠ 0 ∧
        ∀ i, degree < i → i < 64 * words.size →
          words[i / 64]! &&& (1 <<< (i % 64)) = 0)
  -- Zero: words = #[], degree = 0.
  -- Nonzero: last word nonzero, bit `degree` set, no bits above.
```

- Addition: word-by-word XOR
- Multiplication: schoolbook or Karatsuba on 64-bit blocks, where
  each block multiply uses carry-less multiply via `@[extern]`
  calling a C wrapper that uses CLMUL on x86 (with compile-time
  feature detection) and a portable shift-and-XOR fallback on other
  architectures.
- Division with remainder (for polynomial GCD, modular reduction)
- GCD and extended GCD over `GF2Poly`
- Shift operations (multiply/divide by x^k)

**Key properties:**
- Ring axioms (char 2 gives `a + a = 0`; mul commutativity from the
  convolution definition over a commutative coefficient ring)
- `GF2Poly` is a Euclidean domain (degree function is the norm)
- Equivalence: `GF2Poly ≃+* FpPoly 2` (unpack/repack, in hex-gf2-mathlib)

**Carry-less multiply.** The `@[extern]` story mirrors hex-arith's
GMP externals: the pure Lean `clmul` is the logical definition used
in proofs; the C wrapper replaces it at runtime. Correctness of the
extern is trusted (same as `mpz_gcd`, `mpz_mul`, etc.).

The pure Lean fallback (also used as the logical definition):
```
def clmul (a b : UInt64) : UInt64 × UInt64 :=
  -- 64 iterations of: if bit i of b is set, XOR a << i into
  -- 128-bit accumulator (hi, lo). Must handle shift-past-64
  -- correctly by splitting into high/low word contributions.
```
Slower than hardware CLMUL but avoids the per-operation Barrett
overhead of the generic `ZMod64 2` path.

**GF(2^n) elements.** Elements of `GF(2^n)` are polynomials of degree
< n over F_2, reduced modulo an irreducible of degree n. Two cases:

1. **n < 64**: a single `UInt64` suffices. The irreducible modulus
   `x^n + (lower terms)` is stored as `irr : UInt64` containing only
   the lower n coefficients (the leading `x^n` term is implicit).
   Addition is XOR, multiplication is CLMUL followed by reduction
   mod the irreducible (a few XORs with precomputed masks). This
   gives `GF(2^8)` for AES, `GF(2^16)` for coding theory, etc.
   (n = 64 excluded because reduction requires `1 <<< n` which is
   undefined for `UInt64` shift-by-64; use `GF2nPoly` for n ≥ 64.)

2. **n ≥ 64**: use `GF2Poly` with modular reduction after each
   multiply. `GF(2^64)`, `GF(2^128)` for GCM/GHASH, `GF(2^256)`
   for some post-quantum schemes.

```lean
/-- GF(2^n) packed into a single UInt64. Requires n < 64.
    irr stores the lower n coefficients of a monic degree-n
    irreducible; the leading x^n term is implicit. -/
structure GF2n (n : Nat) (irr : UInt64)
    (hn : 0 < n) (hn64 : n < 64)
    (hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)) where
  val : UInt64
  val_lt : val.toNat < 2^n

/-- GF(2^n) for arbitrary n, using GF2Poly.
    This is a quotient ring F_2[x]/(f), parallel to hex-gfq-ring
    but over GF2Poly instead of FpPoly. Operations: add via XOR,
    multiply via CLMUL then reduce mod f. -/
structure GF2nPoly (f : GF2Poly) (hirr : GF2Poly.Irreducible f) where
  val : GF2Poly
  val_reduced : val.IsZero ∨ val.degree < f.degree
```

For the small case, `GF2n` gets `Field` and `Fintype` instances
directly (field axioms from the irreducibility proof `hirr`).
For large n, `GF2nPoly` builds its own quotient-field structure
(parallel to hex-gfq-ring/hex-gfq-field, but over the packed
`GF2Poly` representation rather than `FpPoly`).

The ring equivalences `GF2n ≃+* FiniteField 2 f hirr` and
`GF2nPoly ≃+* FiniteField 2 f hirr` live in hex-gf2-mathlib,
transferring via `GF2Poly ≃+* FpPoly 2`.
