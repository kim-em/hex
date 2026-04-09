# Prior art

**Isabelle/HOL** (the gold standard): The Innsbruck group verified the
entire Berlekamp-Zassenhaus + LLL pipeline. Degree-500 polynomials factor
at 2.5x Mathematica speed. ~44K lines across multiple AFP entries.

**Baanen et al. (Lean 4)**: Certificate-based irreducibility checking for
the rings-of-integers project. Uses `decide`/`native_decide` on list-based
polynomials. Works but doesn't scale beyond small degrees.

**CoqEAL (Coq)**: Verified Karatsuba, Strassen, Bareiss, Smith normal form.
Refinement-based approach.

**FLINT (C)**: The performance target. Dense `nmod_poly` and `fmpz_poly`
with Barrett reduction, Karatsuba, NTT. Not verified.
