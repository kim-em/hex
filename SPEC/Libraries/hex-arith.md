# hex-arith (no dependencies)

Core integer arithmetic that everything else builds on.

**Contents:**

- Extended GCD for `Nat`, `Int`, and `UInt64`
- Barrett and Montgomery reduction for `UInt64` modular arithmetic
  (see below)
- Modular exponentiation by squaring (using Montgomery internally)
- GMP FFI extra: `@[extern]` wrapper for `mpz_gcdext` — for big-integer
  extended GCD / Bezout computations
- Pure Lean implementations of the same for the proof target

**Barrett reduction** — fast single modular multiplication on `UInt64`
for small moduli (`p < 2^32`). Precompute an approximate reciprocal
of the modulus, then reduce via multiply + shift instead of division.

The restriction `p < 2^32` is essential: it ensures `a * b < p² < 2^64`
fits in a single `UInt64`, so the approximation `q = mulHi(T, pinv)`
works with a 64-bit reciprocal. For `p ≥ 2^32`, use Montgomery.

```lean
structure BarrettCtx (p : UInt64) where
  p_gt : p.toNat > 1
  p_lt : p.toNat < 2^32
  pinv : UInt64
  pinv_eq : pinv = .ofNat (2 ^ 64 / p.toNat)

def BarrettCtx.mk (p : UInt64) (hp : p.toNat > 1) (hlt : p.toNat < 2^32) :
    BarrettCtx p
def BarrettCtx.mulMod (ctx : BarrettCtx p) (a b : UInt64) : UInt64
```

Key properties:
```lean
theorem BarrettCtx.mulMod_lt (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b < p

theorem BarrettCtx.toNat_mulMod (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat

theorem BarrettCtx.mulMod_eq (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.mulMod a b = .mk ⟨(a.toNat * b.toNat) % p.toNat, by omega⟩
```

**Barrett proof organization.** Five layers (three Barrett-specific,
sharing Layers 1–2 with Montgomery). Simpler than Montgomery because
there's no domain conversion or inverse computation, and the product
fits in a single `UInt64`.

*Layer 1 — `HexArith/UInt64/Wide.lean` (shared with Montgomery).*
128-bit arithmetic: `mulHi`, `addCarry`, `subBorrow`. See Montgomery
section below.

*Layer 2 — `HexArith/Nat/ModArith.lean` (shared with Montgomery).*
Nat-level modular lemmas. See Montgomery section below.

*Layer 3 — `HexArith/Barrett/ReduceNat.lean` (pure Nat math).* Barrett
reduction stated and proved at `Nat` with `R = 2^64`. No `UInt64`:

```lean
/-- Barrett reduction at the Nat level.
    Given T = a * b (fits in a single word since p < 2^32),
    pinv = ⌊R / p⌋:
    1. q = ⌊T * pinv / R⌋   — approximate quotient T / p
    2. r = T - q * p          — approximate remainder
    3. if r ≥ p then r - p    — at most one corrective subtraction -/
def barrettReduceNat (p pinv T : Nat) : Nat :=
  let q := T * pinv / R
  let r := T - q * p
  if r ≥ p then r - p else r
```

The key bound: `pinv = ⌊R / p⌋`, so `R/p - 1 < pinv ≤ R/p`.

```lean
theorem barrettReduceNat_eq_mod (hp : 1 < p) (hpinv : pinv = R / p)
    (hT : T < R) :
    barrettReduceNat p pinv T = T % p

theorem barrettReduceNat_lt (hp : 1 < p) (hpinv : pinv = R / p)
    (hT : T < R) :
    barrettReduceNat p pinv T < p
```

Note: the caller provides `T < R` which follows from `a, b < p < 2^32`
giving `T = a * b < 2^64 = R`.

Proof of `barrettReduceNat_eq_mod`:

1. **Quotient bound.** Let `q_exact = T / p` and `q = T * pinv / R`.

   Upper bound (`q ≤ q_exact`): `pinv = ⌊R/p⌋ ≤ R/p`, so
   `T * pinv ≤ T * R/p`, hence `q = ⌊T * pinv / R⌋ ≤ T/p`.

   Lower bound (`q ≥ q_exact - 1`): `pinv ≥ R/p - 1`, so
   `T * pinv ≥ T * (R/p - 1) = T*R/p - T`. Hence
   `T * pinv / R ≥ T/p - T/R`. Since `T < R`, we get `T/R < 1`,
   so `q ≥ ⌊T/p - T/R⌋ ≥ T/p - 1 = q_exact - 1`.

2. **Remainder bound.** `r = T - q*p`. Since `q ≤ q_exact`,
   `r ≥ T mod p ≥ 0`. Since `q ≥ q_exact - 1`,
   `r ≤ T mod p + p < 2p`. And `2p < 2^33 < R`, so `r` fits
   in a single `UInt64`.

3. **Conditional subtraction.** If `r ≥ p`, then `r - p = T mod p`.
   If `r < p`, then `r = T mod p` directly.

*Layer 4 — `HexArith/Barrett/Reduce.lean` (UInt64 bridge).* Executable
Barrett reduction in `UInt64`, proven equivalent to `barrettReduceNat`.
Since `p < 2^32`, the product `T = a * b` fits in a single `UInt64`
(no 128-bit splitting needed):

```lean
def barrettReduce (ctx : BarrettCtx p) (T : UInt64) : UInt64 :=
  let q := mulHi T ctx.pinv
  let r := T - q * p
  if r ≥ p then r - p else r

theorem toNat_barrettReduce (ctx : BarrettCtx p) (T : UInt64)
    (hT : T.toNat < p.toNat * p.toNat) :
    (barrettReduce ctx T).toNat =
      barrettReduceNat p.toNat ctx.pinv.toNat T.toNat
```

The bridge is straightforward: `mulHi T pinv` = `T.toNat * pinv.toNat / R`
by `toNat_mulHi`, and `T - q * p` is safe (no underflow since `q ≤ T/p`
means `q * p ≤ T`). No high-word reasoning needed.

*Layer 5 — `HexArith/Barrett/Context.lean` (user-facing API).*
`BarrettCtx.mulMod` defined as `barrettReduce ctx (a * b)`. The product
`a * b` doesn't overflow because `a < p < 2^32` and `b < p < 2^32`
give `a.toNat * b.toNat < 2^64`. The three user-facing theorems
(`mulMod_lt`, `toNat_mulMod`, `mulMod_eq`) follow from
`toNat_barrettReduce` + `barrettReduceNat_eq_mod`.

**Why Barrett is simpler than Montgomery:** no domain conversion
(no `toMont`/`fromMont`), no Montgomery inverse computation (no
Newton iteration), the product fits in a single word, and the Nat-level
proof is a direct approximation argument rather than a modular-inverse
congruence.

**Montgomery reduction** — optimized for sustained modular arithmetic
(sequences of multiplications with the same modulus, e.g. exponentiation
by squaring, polynomial evaluation over F_p).

Values are stored in Montgomery form: `a` is represented as `a * R mod p`
where `R = 2^64`. Reduction uses the low bits of the product (a mask)
instead of division.

```lean
structure MontCtx (p : UInt64) where
  p_odd : p % 2 = 1
  p' : UInt64
  p'_eq : (p'.toNat * p.toNat) % 2 ^ 64 = 2 ^ 64 - 1
  r2 : UInt64
  r2_eq : r2.toNat = (2 ^ 64 * 2 ^ 64) % p.toNat

def MontCtx.mk (p : UInt64) (hp : p % 2 = 1) : MontCtx p
def MontCtx.toMont (ctx : MontCtx p) (a : UInt64) : UInt64
def MontCtx.fromMont (ctx : MontCtx p) (a : UInt64) : UInt64
def MontCtx.mulMont (ctx : MontCtx p) (a b : UInt64) : UInt64
```

Key properties:
```lean
theorem MontCtx.fromMont_toMont (ctx : MontCtx p) (a : UInt64)
    (ha : a < p) :
    ctx.fromMont (ctx.toMont a) = a

theorem MontCtx.toNat_mulMont (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat

theorem MontCtx.mulMont_eq (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b)) =
      .mk ⟨(a.toNat * b.toNat) % p.toNat, by omega⟩
```

**Montgomery proof organization.** The correctness proof is split into
layers that separate pure math from machine-word encoding. Lean 4 core
provides `UInt64.toNat_add`, `toNat_mul`, `toNat_div`, `toNat_mod`,
`toNat_sub` (all `simp`-tagged), which suffice for overflow reasoning
via `Nat.add_mod`, `Nat.mul_mod`, `Nat.div_add_mod`. There is no
`mulHi`, add-with-carry, or `UInt128` in core — we build those.

*Layer 1 — `HexArith/UInt64/Wide.lean` (shared with Barrett).* 128-bit
arithmetic helpers on `UInt64`:

```lean
def UInt64.mulHi (a b : UInt64) : UInt64 :=
  .ofNat (a.toNat * b.toNat / 2^64)
  -- Logical definition; `@[implemented_by]` C extern for runtime.

def UInt64.addCarry (a b : UInt64) (cin : Bool) : UInt64 × Bool
def UInt64.subBorrow (a b : UInt64) (bin : Bool) : UInt64 × Bool

theorem UInt64.toNat_mulHi (a b : UInt64) :
    (mulHi a b).toNat = a.toNat * b.toNat / 2^64
theorem UInt64.mulHi_mulLo (a b : UInt64) :
    (mulHi a b).toNat * 2^64 + (a * b).toNat = a.toNat * b.toNat
theorem UInt64.toNat_addCarry (a b : UInt64) (cin : Bool) :
    let (s, cout) := addCarry a b cin
    s.toNat + cout.toNat * 2^64 = a.toNat + b.toNat + cin.toNat
```

Carries are `Bool` (not `UInt64`) — no preconditions needed. This is
the only layer that touches overflow semantics.

*Layer 2 — `HexArith/Nat/ModArith.lean`.* Small file of `Nat`-level
modular lemmas that Lean 4 core lacks: exact division (`R ∣ n → n / R * R = n`),
mod cancellation, coprimality/cancellation for odd `p` and `R = 2^k`,
powers-of-two identities, divisibility transfer from `p·p' ≡ -1 (mod R)`.
Needed because `omega` won't solve nonlinear modular goals.

*Layer 3 — `HexArith/Montgomery/RedcNat.lean` (pure Nat math).* REDC
stated and proved at `Nat` with `R = 2^64`. No `UInt64` appears:

```lean
def redcNat (p p' T : Nat) : Nat :=
  let m := (T % R) * p' % R
  let u := (T + m * p) / R
  if u < p then u else u - p

theorem redcNat_eq_mod (hp_pos : 0 < p) (hp_lt : p < R)
    (hpp' : p * p' % R = R - 1) (hT : T < p * R) :
    redcNat p p' T * R % p = T % p

theorem redcNat_lt (hp_pos : 0 < p) (hp_lt : p < R)
    (hpp' : p * p' % R = R - 1) (hT : T < p * R) :
    redcNat p p' T < p

theorem redcNat_u_lt_two_p (hp_pos : 0 < p) (hp_lt : p < R)
    (hpp' : p * p' % R = R - 1) (hT : T < p * R) :
    (T + ((T % R) * p' % R) * p) / R < 2 * p
```

Proof: `T + m·p ≡ 0 (mod R)` by choice of `p'`, so division is exact;
`m < R` and `T < p·R` give `T + m·p < 2·p·R`, so `u < 2p`; conditional
subtraction lands in `[0, p)`.

*Layer 4 — `HexArith/Montgomery/InvNat.lean` (Montgomery inverse).*
Computes `p'` with `p·p' ≡ −1 (mod 2^64)`. Strategy: prove the
*positive* inverse `p·x ≡ 1 (mod 2^64)` by Newton/Hensel iteration,
then negate (`p' = R - x`):

```lean
theorem newton_step (hp_odd : p % 2 = 1) (k : Nat)
    (hxk : p * x % 2^k = 1) :
    p * (x * (2 - p * x)) % 2^(2*k) = 1

-- Seed: for odd p, p·p ≡ 1 (mod 8)
-- 6 Newton doublings from 3-bit seed: 3 → 6 → 12 → 24 → 48 → 64+ bits
def montPosInv (p : UInt64) : UInt64  -- iterate x ↦ x*(2 - p*x) in UInt64

theorem montPosInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montPosInv p).toNat % 2^64 = 1

def montInv (p : UInt64) : UInt64 := 0 - montPosInv p

theorem montInv_spec (p : UInt64) (hp_odd : p.toNat % 2 = 1) :
    p.toNat * (montInv p).toNat % 2^64 = 2^64 - 1
```

Note: `2 - p*x` is computed in wrapping UInt64 arithmetic (underflows
in `Nat`). The Nat-level proof works mod `2^(2k)`.

*Layer 5 — `HexArith/Montgomery/Redc.lean` (UInt64 bridge).* Executable
REDC in `UInt64`, proven equivalent to `redcNat` via intermediate lemmas
(not definitional equality — executable code uses `mulHi`/carries while
`redcNat` uses division). Key subtlety: `u < 2p` may exceed `UInt64.size`
when `p` is near `2^64`, so `u` is a 65-bit value `(carry, lo) : Bool × UInt64`:

```lean
def redc (ctx : MontCtx p) (Thi Tlo : UInt64) : UInt64 :=
  let m := Tlo * ctx.p'
  let (_, c1) := UInt64.addCarry Tlo (m * p) false
  let (addHi, c2) := UInt64.addCarry Thi (mulHi m p) c1
  if c2 then addHi - p
  else if addHi ≥ p then addHi - p else addHi

-- Intermediate bridge lemmas
theorem redc_m_spec ...    -- m.toNat = (T % R) * p'.toNat % R
theorem redc_u_spec ...    -- (c2, addHi) represents u = (T + m*p) / R
theorem redc_sub_spec ...  -- conditional subtraction matches redcNat

theorem toNat_redc (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * 2^64 < p.toNat * 2^64) :
    (redc ctx Thi Tlo).toNat =
      redcNat p.toNat ctx.p'.toNat (Tlo.toNat + Thi.toNat * 2^64)
```

*Layer 6 — `HexArith/Montgomery/Context.lean` (user-facing API).*
Definitions of `toMont`, `fromMont`, `mulMont` in terms of `redc`,
plus derived Nat-level projections (`p_pos`, `p_lt_R`, `p_odd_nat`)
proved once on `MontCtx`, bounds/closure lemmas (`toMont_lt`,
`mulMont_lt`), a Montgomery domain invariant (`mulMont_repr`), and
the three user-facing theorems (`fromMont_toMont`, `toNat_mulMont`,
`mulMont_eq`) derived from the invariant. `r2` is computed by repeated
doubling in `MontCtx.mk`, not via Barrett (avoids circular dependency).

**When to use which:** Barrett for one-off or few modular operations.
Montgomery for hot loops (exponentiation, Frobenius map, polynomial
multiplication over F_p) where the conversion overhead is amortized.

**Extended GCD:**
```lean
def extGcd (a b : Nat) : Nat × Int × Int

theorem extGcd_fst (a b : Nat) : (extGcd a b).1 = Nat.gcd a b

theorem extGcd_bezout (a b : Nat) :
    let (g, s, t) := extGcd a b
    s * a + t * b = g
```
Also for `Int` and `UInt64` variants.

**Modular exponentiation:**
```lean
def powMod (a n p : Nat) : Nat  -- uses Montgomery internally

theorem powMod_eq (a n p : Nat) (hp : p > 0) :
    powMod a n p = a ^ n % p
```

**Binomial coefficients and Fermat's little theorem:**

`Nat.choose` is in Mathlib, not Init, so we define it here
(standard recursive definition). We prove the key lemma and Fermat's
little theorem:
```lean
theorem Nat.choose_prime_dvd (hp : Nat.Prime p) (hk : 0 < k) (hk' : k < p) :
    p ∣ Nat.choose p k

theorem Nat.add_pow_prime_mod (hp : Nat.Prime p) (a b : Nat) :
    (a + b) ^ p % p = (a ^ p + b ^ p) % p

theorem Nat.pow_prime_mod (hp : Nat.Prime p) (a : Nat) :
    a ^ p % p = a % p
```
Proof: `choose_prime_dvd` by Euclid's lemma (since `k! * C(p,k)` has
factor `p` but `gcd(p, k!) = 1`). `add_pow_prime_mod` follows
(all middle binomial terms vanish mod p). `pow_prime_mod` by induction
on `a`: base `0^p = 0`, step uses `add_pow_prime_mod` with `b = 1`.

**Euclid's lemma:**
```lean
theorem Nat.Prime.dvd_mul (hp : Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b
```
Proof via extended GCD: if `p ∤ a` then `gcd(a, p) = 1`, Bezout gives
`s * a + t * p = 1`, multiply by `b`, since `p ∣ a * b` conclude `p ∣ b`.

**Note:** `Nat.gcd` already exists with GMP-backed `mpz_gcd`. We build on
it for extended GCD. The pure Lean `extGcd` is the logical definition used
in proofs; the GMP `@[extern]` for `mpz_gcdext` replaces it at runtime,
trusted in the same way as every other `@[extern]` in Lean.
