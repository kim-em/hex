# hex-mod-arith (modular arithmetic, depends on hex-arith)

Arithmetic in `Z/nZ` with `UInt64`-backed coefficients.

**Contents:**
- `ZMod64 (p : Nat)` — a `UInt64` with proof `val.toNat < p`
- Addition, subtraction, multiplication (using Barrett/Montgomery from
  hex-arith for the `UInt64` modular operations)
- Inversion via extended GCD (for prime moduli)
- Exponentiation by squaring
- `Lean.Grind.CommRing (ZMod64 p)` instance and `IsCharP (ZMod64 p) p`

**Key properties:**
- Ring axioms proved directly from the modular arithmetic definitions.
  Associativity and distributivity of multiplication reduce to
  `Nat.mod` properties via Barrett/Montgomery correctness from
  hex-arith.
- `inv a * a = 1` when `Nat.Coprime a.val p` — via extended GCD
  from hex-arith: `s * a + t * p = 1` gives `s mod p` as the inverse.
- No zero divisors for prime `p`: `a * b = 0 → a = 0 ∨ b = 0` — via
  Euclid's lemma from hex-arith.
- Fermat's little theorem: `a ^ p = a` — lifts directly from
  `Nat.pow_prime_mod` in hex-arith.

**Note:** `Fin n` already has `Lean.Grind.CommRing` and `IsCharP`. We
build `ZMod64` for performance (Barrett reduction instead of naive modular
arithmetic) and for cleaner API (explicit prime parameter, field operations).
