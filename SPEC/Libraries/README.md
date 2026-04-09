# Libraries

- **hex-arith** — extended GCD, Barrett/Montgomery reduction, binomial coefficients, Fermat's little theorem
- **hex-poly** — dense `Array`-backed polynomial representation
- **hex-matrix** — dense matrices as `Vector (Vector R m) n`, RREF, Bareiss determinant, span, nullspace
- **hex-gram-schmidt** — Gram-Schmidt orthogonalization, GS coefficients, Gram determinants, update formulas under row operations
- **hex-mod-arith** — `ZMod64 p`: `UInt64`-backed arithmetic in `Z/pZ`
- **hex-poly-fp** — polynomials over `F_p`, Frobenius map, square-free decomposition, lazy reduction for small p
- **hex-gf2** — packed bitwise polynomials over `F_2` (XOR + CLMUL), `GF(2^n)` elements
- **hex-poly-z** — polynomials over `Z`, content/primitive part, Mignotte bound
- **hex-berlekamp** — Berlekamp factoring and Rabin irreducibility test over `F_p`
- **hex-hensel** — Hensel lifting from `mod p` to `mod p^k`
- **hex-lll** — LLL lattice basis reduction
- **hex-berlekamp-zassenhaus** — complete factoring of `Z[x]`
- **hex-conway** — Conway polynomial database
- **hex-gfq-ring** — quotient ring `F_p[x]/(f)`
- **hex-gfq-field** — field structure when `f` is irreducible
- **hex-gfq** — convenience wrapper: `GFq p n` using Conway polynomials

**Mathlib bridge libraries** (each depends on a computational lib + Mathlib,
proving correspondence with Mathlib's mathematical definitions):

- **hex-mod-arith-mathlib** — `ZMod64 p ≃+* ZMod p`
- **hex-poly-mathlib** — `DensePoly R ≃+* Polynomial R`
- **hex-matrix-mathlib** — matrix equivalence, `det` agreement, rank = `Matrix.rank`, nullspace = `LinearMap.ker`, row ops = transvections
- **hex-gram-schmidt-mathlib** — `GramSchmidt.Int.basis` = Mathlib's `gramSchmidt`
- **hex-poly-z-mathlib** — `DensePoly Int ≃+* Polynomial ℤ`, Mignotte bound (via Mathlib's Mahler measure)
- **hex-berlekamp-mathlib** — `Decidable (Irreducible f)` for `Polynomial (ZMod p)`
- **hex-hensel-mathlib** — Hensel correctness, uniqueness, `coprime_mod_p_lifts`
- **hex-lll-mathlib** — lattice = `Submodule ℤ`, short vector bound
- **hex-gf2-mathlib** — `GF2Poly ≃+* FpPoly 2`, `GF2n`/`GF2nPoly ≃+* FiniteField 2 f hirr`
- **hex-gfq-mathlib** — `GFq p n ≃+* GaloisField p n`
- **hex-berlekamp-zassenhaus-mathlib** — unconditional factoring correctness, `Decidable (Irreducible f)` for `Polynomial ℤ`

## Implementation dependencies

Each library with its immediate dependencies:

- **hex-arith** — (none)
- **hex-poly** — (none)
- **hex-matrix** — (none)
- **hex-mod-arith** — hex-arith
- **hex-gram-schmidt** — hex-matrix
- **hex-lll** — hex-gram-schmidt
- **hex-poly-fp** — hex-poly, hex-mod-arith
- **hex-poly-z** — hex-poly
- **hex-berlekamp** — hex-poly-fp, hex-matrix, hex-gfq-ring
- **hex-hensel** — hex-poly-fp, hex-poly-z
- **hex-conway** — hex-berlekamp
- **hex-gfq-ring** — hex-poly-fp
- **hex-gfq-field** — hex-berlekamp
- **hex-gfq** — hex-gfq-field, hex-conway
- **hex-gf2** — hex-poly
- **hex-berlekamp-zassenhaus** — hex-berlekamp, hex-hensel, hex-lll

Mathlib bridge libraries (each also depends on Mathlib):

- **hex-mod-arith-mathlib** — hex-mod-arith
- **hex-poly-mathlib** — hex-poly
- **hex-poly-z-mathlib** — hex-poly-z, hex-poly-mathlib
- **hex-matrix-mathlib** — hex-matrix
- **hex-gram-schmidt-mathlib** — hex-gram-schmidt
- **hex-lll-mathlib** — hex-lll
- **hex-berlekamp-mathlib** — hex-berlekamp, hex-poly-mathlib, hex-mod-arith-mathlib
- **hex-hensel-mathlib** — hex-hensel, hex-poly-mathlib
- **hex-gf2-mathlib** — hex-gf2, hex-poly-fp, hex-gfq-field
- **hex-gfq-mathlib** — hex-gfq
- **hex-berlekamp-zassenhaus-mathlib** — hex-berlekamp-zassenhaus, hex-poly-z-mathlib

LLL is completely independent of the polynomial pipeline. The only
point of contact is at the very top (Berlekamp-Zassenhaus).

## Library DAG

Three independent roots: hex-poly, hex-arith, hex-matrix.

```
      hex-poly     hex-arith      hex-matrix
       /     \          |            /       \
      /       \     hex-mod-arith  /  hex-gram-schmidt
     /         \       /           /         |
hex-poly-z  hex-poly-fp         /       hex-lll
     \        /       |          /         /
     hex-hensel  hex-gfq-ring /         /
               \       |       /         /
                \  hex-berlekamp       /
                 \      |              /
                  hex-berlekamp-zassenhaus
```

Additional libraries (finite field construction, GF(2)):
```
hex-poly ── hex-gf2

        hex-berlekamp
         /          \
  hex-gfq-field  hex-conway
         \          /
          hex-gfq
```

## Index

- [hex-arith.md](hex-arith.md) — extended GCD, Barrett/Montgomery reduction, binomial coefficients, Fermat's little theorem
- [hex-matrix.md](hex-matrix.md) — dense matrices, RREF, Bareiss determinant, span, nullspace
- [hex-matrix-mathlib.md](hex-matrix-mathlib.md) — matrix equivalence with Mathlib, determinant/rank/nullspace correspondence
- [hex-mod-arith.md](hex-mod-arith.md) — `ZMod64 p`: `UInt64`-backed arithmetic in `Z/pZ`
- [hex-mod-arith-mathlib.md](hex-mod-arith-mathlib.md) — `ZMod64 p ≃+* ZMod p`
- [hex-poly.md](hex-poly.md) — dense polynomial library, operations, GCD, CRT
- [hex-poly-mathlib.md](hex-poly-mathlib.md) — `DensePoly R ≃+* Polynomial R`
- [hex-poly-fp.md](hex-poly-fp.md) — polynomials over `F_p`, Frobenius, square-free decomposition
- [hex-gf2.md](hex-gf2.md) — packed bitwise polynomials over `F_2`, `GF(2^n)` elements
- [hex-gf2-mathlib.md](hex-gf2-mathlib.md) — `GF2Poly ≃+* FpPoly 2`, `GF2n`/`GF2nPoly ≃+* FiniteField 2 f hirr`
- [hex-poly-z.md](hex-poly-z.md) — polynomials over `Z`, content/primitive part, Mignotte bound
- [hex-poly-z-mathlib.md](hex-poly-z-mathlib.md) — Mignotte bound proof via Mathlib's Mahler measure
- [hex-berlekamp.md](hex-berlekamp.md) — Berlekamp factoring and Rabin irreducibility test
- [hex-berlekamp-mathlib.md](hex-berlekamp-mathlib.md) — Berlekamp/Rabin correctness proofs via Euclidean domain theory
- [hex-hensel.md](hex-hensel.md) — Hensel lifting algorithms
- [hex-hensel-mathlib.md](hex-hensel-mathlib.md) — Hensel correctness, uniqueness, coprimality lifting
- [hex-conway.md](hex-conway.md) — Conway polynomial database
- [hex-gfq-ring.md](hex-gfq-ring.md) — quotient ring `F_p[x]/(f)`
- [hex-gfq-field.md](hex-gfq-field.md) — field structure when `f` is irreducible
- [hex-gfq.md](hex-gfq.md) — convenience wrapper `GFq p n` using Conway polynomials
- [hex-gfq-mathlib.md](hex-gfq-mathlib.md) — `GFq p n ≃+* GaloisField p n`
- [hex-gram-schmidt.md](hex-gram-schmidt.md) — Gram-Schmidt orthogonalization, coefficients, Gram determinants
- [hex-gram-schmidt-mathlib.md](hex-gram-schmidt-mathlib.md) — correspondence with Mathlib's `gramSchmidt`
- [hex-lll.md](hex-lll.md) — LLL lattice basis reduction algorithm and proofs
- [hex-lll-mathlib.md](hex-lll-mathlib.md) — lattice = `Submodule Z`, short vector bound
- [hex-berlekamp-zassenhaus.md](hex-berlekamp-zassenhaus.md) — complete factoring of `Z[x]`
- [hex-berlekamp-zassenhaus-mathlib.md](hex-berlekamp-zassenhaus-mathlib.md) — unconditional factoring correctness
