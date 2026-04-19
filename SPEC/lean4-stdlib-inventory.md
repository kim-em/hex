# Lean 4 stdlib inventory (v4.28.0)

What we get for free and what we need to build.

**Available:**
- `Nat.gcd` / `Int.gcd` — GMP-backed via `@[extern "lean_nat_gcd"]`
- `Nat.divExact` / `Int.divExact` — GMP-backed (`mpz_divexact`), requires
  divisibility proof; faster than regular division
- `Nat.Coprime` — `gcd m n = 1`, decidable, with lemmas
- `Nat.lcm` / `Int.lcm`
- `Rat` — proper rational field with `Lean.Grind.Field` instance
- `Vector α n` — `Array α` with size proof, rich API (~19 files)
- `Fin n` — modular arithmetic with `Lean.Grind.CommRing` and `IsCharP`
- `BitVec w` — `Fin (2^w)`, extensive API, `bv_decide` support
- `Std.HashMap` / `Std.ExtHashMap` — the latter has extensionality
- `Lean.Grind.{Semiring, Ring, CommSemiring, CommRing, Field}` hierarchy

**Not available (we build):**
- Extended GCD / Bezout coefficients — completely absent
- Modular exponentiation — absent as a stdlib primitive, but this
  project's specified path is a pure Lean implementation
- Modular inverse — absent as a stdlib primitive, but this project's
  specified path is via extended GCD
- Primality testing — absent (not needed for this project; Berlekamp-
  Zassenhaus only needs small known primes)
- Polynomial types — none (only internal `grind` polynomials)
- Matrix types — none
- Finite field types / `ZMod` — absent (only `Fin n`)

**GMP primitives to expose (via `@[extern]` FFI, ideally upstreamed):**
- `mpz_gcdext` — extended GCD with Bezout coefficients

These would live in `hex-gmp-extras` or be proposed as upstream additions
to the Lean runtime.
