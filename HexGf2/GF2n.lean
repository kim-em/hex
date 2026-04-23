import HexGf2.FiniteExtension

/-!
Executable small-word arithmetic for packed `GF(2^n)` extensions.

This module adds the Phase 1 operation layer for the single-word `GF2n`
carrier. Addition is XOR on representatives; multiplication uses the
carry-less `clmul` boundary followed by executable reduction modulo the
implicit monic irreducible `x^n + irr`.
-/

namespace HexGf2

namespace GF2n

/-- The explicit packed modulus `x^n + irr` as a natural number. -/
def modulusNat (n : Nat) (irr : UInt64) : Nat :=
  (2 ^ n) + irr.toNat

/-- Bitmask selecting the low `n` coefficients of a packed `GF(2^n)` element. -/
def mask (n : Nat) : UInt64 :=
  UInt64.ofNat (2 ^ n - 1)

/--
Reduce a packed polynomial representative modulo the implicit monic modulus.

The input is treated as a natural-number bitset for the executable Phase 1
scaffold; later work can replace the implementation with a more refined proof-
oriented reduction routine if needed.
-/
private def reduceNatAux (n : Nat) (irr : UInt64) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      if acc < 2 ^ n then
        acc
      else
        let shift := acc.log2 - n
        let modulus := modulusNat n irr <<< shift
        reduceNatAux n irr fuel (Nat.xor acc modulus)

/-- Reduce a natural-number representative into the canonical `n`-bit range. -/
def reduceNat (n : Nat) (irr : UInt64) (value : Nat) : Nat :=
  reduceNatAux n irr (2 * n + 1) value

/-- Reduce a 128-bit carry-less product modulo the implicit monic modulus. -/
def reduceWord (n : Nat) (irr : UInt64) (hi lo : UInt64) : UInt64 :=
  UInt64.ofNat (reduceNat n irr (lo.toNat + hi.toNat * 2 ^ 64))

/-- Canonical constructor for packed `GF(2^n)` representatives. -/
def ofUInt64 {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}
    (value : UInt64) : GF2n n irr hn hn64 hirr where
  val := value &&& mask n
  val_lt := by
    sorry

/-- The packed zero element of `GF(2^n)`. -/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Zero (GF2n n irr hn hn64 hirr) where
  zero := ofUInt64 0

/-- The packed one element of `GF(2^n)`. -/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    One (GF2n n irr hn hn64 hirr) where
  one := ofUInt64 1

/-- Addition in `GF(2^n)` is XOR on packed representatives. -/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Add (GF2n n irr hn hn64 hirr) where
  add x y := ofUInt64 (x.val ^^^ y.val)

/--
Multiplication in `GF(2^n)` uses carry-less multiply followed by reduction
modulo the implicit monic irreducible.
-/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Mul (GF2n n irr hn hn64 hirr) where
  mul x y :=
    let (hi, lo) := clmul x.val y.val
    ofUInt64 (reduceWord n irr hi lo)

/-- Reduction lands in the expected packed range. -/
theorem reduceNat_lt_pow (n : Nat) (irr : UInt64) (value : Nat) :
    reduceNat n irr value < 2 ^ n := by
  sorry

/-- The canonical constructor stores exactly the masked representative. -/
theorem ofUInt64_val {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}
    (value : UInt64) :
    (ofUInt64 (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr) value).val =
      value &&& mask n := by
  rfl

/-- Packed addition is definitionally XOR followed by canonical masking. -/
theorem add_val {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}
    (x y : GF2n n irr hn hn64 hirr) :
    (x + y).val = (x.val ^^^ y.val) &&& mask n := by
  rfl

/-- Packed multiplication is definitionally CLMUL followed by reduction. -/
theorem mul_val {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}
    (x y : GF2n n irr hn hn64 hirr) :
    let (hi, lo) := clmul x.val y.val
    (x * y).val = reduceWord n irr hi lo &&& mask n := by
  rfl

/-- The zero representative is the zero packed word. -/
theorem zero_val {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    (0 : GF2n n irr hn hn64 hirr).val = 0 := by
  sorry

/-- The one representative is the low packed bit. -/
theorem one_val {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    (1 : GF2n n irr hn hn64 hirr).val = 1 := by
  sorry

end GF2n

end HexGf2
