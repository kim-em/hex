# Conformance testing

Every computational library is tested against reference implementations:

1. Generate random inputs (polynomials, lattice bases, etc.)
2. Compute results in both Lean and a reference (FLINT via FFI, SageMath,
   fpLLL) and compare
3. For polynomial factoring, cross-check factorizations against FLINT
   and verify certificates produced by the Lean algorithms

SageMath and FLINT are used for **testing**, not for algorithms — the
distinction is that all computation runs in Lean, and external tools
only serve as an independent oracle for conformance checking.
