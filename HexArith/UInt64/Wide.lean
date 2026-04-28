/-!
Wide-word helper operations for `UInt64`.

This module provides the executable logical definitions of fused and projected
`UInt64 × UInt64` products together with add-with-carry and
subtract-with-borrow operations. Later Barrett and Montgomery reductions use
these operations as the only interface to machine-word overflow behavior.
-/
namespace UInt64

/-- The radix for a single `UInt64` word. -/
def word : Nat := 2 ^ 64

/-- The high 64 bits of the product `a * b`, viewed in radix `2^64`. -/
@[extern "lean_hex_uint64_mul_hi"]
def mulHi (a b : UInt64) : UInt64 :=
  .ofNat (a.toNat * b.toNat / word)

/-- The full `UInt64 × UInt64` product, split into high and low radix-`2^64` words. -/
@[extern "lean_hex_uint64_mul_full"]
def mulFull (a b : UInt64) : UInt64 × UInt64 :=
  let p := a.toNat * b.toNat
  (.ofNat (p / word), .ofNat p)

/--
Add `a`, `b`, and an incoming carry bit, returning the wrapped low word and the
outgoing carry bit.
-/
@[extern "lean_hex_uint64_add_carry"]
def addCarry (a b : UInt64) (cin : Bool) : UInt64 × Bool :=
  let total := a.toNat + b.toNat + cin.toNat
  (.ofNat total, decide (word ≤ total))

/--
Subtract `b` and an incoming borrow bit from `a`, returning the wrapped low
word and the outgoing borrow bit.
-/
@[extern "lean_hex_uint64_sub_borrow"]
def subBorrow (a b : UInt64) (bin : Bool) : UInt64 × Bool :=
  let rhs := b.toNat + bin.toNat
  if rhs ≤ a.toNat then
    (.ofNat (a.toNat - rhs), false)
  else
    (.ofNat (word + a.toNat - rhs), true)

/-- `mulHi` agrees with Nat-level division by `2^64`. -/
theorem toNat_mulHi (a b : UInt64) :
    (mulHi a b).toNat = a.toNat * b.toNat / word := by
  sorry

/-- `mulFull` agrees with Nat-level division and remainder by `2^64`. -/
theorem toNat_mulFull (a b : UInt64) :
    let (hi, lo) := mulFull a b
    hi.toNat = a.toNat * b.toNat / word ∧
    lo.toNat = a.toNat * b.toNat % word := by
  sorry

/--
Splitting the product into high and low words reconstructs the original
Nat-level product.
-/
theorem mulHi_mulLo (a b : UInt64) :
    (mulHi a b).toNat * word + (a * b).toNat = a.toNat * b.toNat := by
  sorry

/--
`addCarry` represents exact Nat addition split into a low word and a carry bit.
-/
theorem toNat_addCarry (a b : UInt64) (cin : Bool) :
    let (s, cout) := addCarry a b cin
    s.toNat + cout.toNat * word = a.toNat + b.toNat + cin.toNat := by
  sorry

/--
`subBorrow` represents exact subtraction with borrow after one-word wrapping.
-/
theorem toNat_subBorrow (a b : UInt64) (bin : Bool) :
    let (d, bout) := subBorrow a b bin
    d.toNat + bout.toNat * word + (b.toNat + bin.toNat) = a.toNat + word := by
  sorry

end UInt64
