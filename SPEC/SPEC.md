# hex — Verified Computational Algebra in Lean 4

A collection of cooperating Lean 4 libraries providing performant, verified
algorithms for computational algebra: polynomial arithmetic, factoring,
irreducibility testing, finite field construction, lattice basis reduction,
and related tools.

## What we're building

The end state is a verified Berlekamp-Zassenhaus factoring pipeline for
polynomials over the integers, with LLL lattice basis reduction for the
factor recombination step. All algorithms are implemented and run natively
in Lean 4 — no external CAS in the loop. The pipeline produces machine-checked
proofs of correctness alongside its computational results.

The computational core is Mathlib-free: dense `Array`-backed polynomials with
`UInt64` coefficients for finite-field arithmetic, Barrett/Montgomery reduction
for modular operations, and GMP FFI for big-integer primitives. Separate
Mathlib bridge libraries prove correspondence with Mathlib's mathematical
definitions (e.g. `DensePoly R ≃+* Polynomial R`, `ZMod64 p ≃+* ZMod p`,
`GFq p n ≃+* GaloisField p n`), transferring deep correctness results from
Mathlib's abstract algebra without imposing Mathlib as a dependency on the
computational code.

The library DAG has three independent roots — polynomial arithmetic, integer
arithmetic, and matrix operations — meeting at the top in
Berlekamp-Zassenhaus. This structure allows parallel development: LLL has no
dependency on polynomial arithmetic, Hensel lifting is independent of LLL,
and all proof work is fully parallelizable once theorem statements are in
place.

## Applications

**Cryptographic field construction:** To build `GF(2^128)` for AES, you
need an irreducible polynomial of degree 128 over `F_2`. With
hex-berlekamp, produce a Lean proof that it's irreducible.

**Coding theory:** Reed-Solomon and BCH codes need irreducible polynomials
over finite fields. Verified factoring provides certified generator
polynomials.

**Number theory:** Computing rings of integers requires factoring
polynomials over Z. The Baanen et al. project currently delegates to
SageMath with unverified certificates — this replaces that dependency.

**Cryptanalysis:** LLL is the core tool for lattice-based attacks. A
verified LLL gives confidence in attack results.

## Navigation

- [Design principles](design-principles.md)
- [Lean 4 stdlib inventory](lean4-stdlib-inventory.md)
- [Libraries](Libraries/) (DAG + per-library docs)
- [Testing](testing.md)
- [Prior art](prior-art.md)
- [Future work](future-work.md)
