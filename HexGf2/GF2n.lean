import HexGf2.FiniteExtension

/-!
Executable small-word arithmetic for packed `GF(2^n)` extensions.

This module adds the Phase 1 operation layer for the single-word `GF2n`
carrier. Addition is XOR on representatives; multiplication uses the
carry-less `clmul` boundary followed by executable reduction modulo the
implicit monic irreducible `x^n + irr`. Mathlib-facing `Field` and
`Fintype` scaffolding for this carrier lives in `HexGf2Mathlib.GF2n`.
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

/-- Packed `GF(2^n)` elements are determined by their canonical word. -/
@[ext] theorem ext {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}
    {x y : GF2n n irr hn hn64 hirr} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  simp

/-- Decidable equality reduces to equality of canonical packed representatives. -/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    DecidableEq (GF2n n irr hn hn64 hirr) := by
  intro x y
  by_cases h : x.val = y.val
  · exact isTrue (ext h)
  · exact isFalse (fun hxy => h (congrArg GF2n.val hxy))

/-- Executable search for a multiplicative inverse among canonical representatives. -/
def inv {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}
    (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if _h0 : a = 0 then
    0
  else
    match (List.range (2 ^ n)).find? fun k =>
        decide (((a *
          ofUInt64 (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr)
            (UInt64.ofNat k)).val = 1)) with
    | some k =>
        ofUInt64 (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr)
          (UInt64.ofNat k)
    | none => 0

/-- Negation is the identity in characteristic two. -/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Neg (GF2n n irr hn hn64 hirr) where
  neg a := a

/-- Subtraction agrees with addition in characteristic two. -/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Sub (GF2n n irr hn hn64 hirr) where
  sub a b := a + b

/-- The executable inverse uses the canonical representative search. -/
instance {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Inv (GF2n n irr hn hn64 hirr) where
  inv := inv

/-- The executable inverse returns zero on the zero element. -/
theorem inv_zero {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    inv (0 : GF2n n irr hn hn64 hirr) = 0 := by
  simp [inv]

/-- Nonzero packed representatives multiply with `inv` to the packed one. -/
theorem mul_inv_cancel {n : Nat} {irr : UInt64}
    {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}
    (a : GF2n n irr hn hn64 hirr) (ha : a ≠ 0) :
    a * inv a = 1 := by
  sorry

end GF2n

end HexGf2
