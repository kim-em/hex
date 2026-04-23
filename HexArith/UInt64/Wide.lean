/-!
Wide-word helpers for `UInt64`.

This module provides the Phase 1 scaffold for shared 128-bit-style
arithmetic operations used by Barrett and Montgomery reduction.
-/

namespace UInt64

/-- The radix for splitting a 128-bit product into high and low 64-bit words. -/
private def wordBase : Nat :=
  2 ^ 64

/--
Return the high 64-bit word of the full product `a * b`, viewed as a
128-bit natural number.
-/
def mulHi (a b : UInt64) : UInt64 :=
  .ofNat (a.toNat * b.toNat / wordBase)

/--
Add two words with an incoming carry bit, returning the low word and the
outgoing carry bit.
-/
def addCarry (a b : UInt64) (cin : Bool) : UInt64 × Bool :=
  let total := a.toNat + b.toNat + cin.toNat
  (.ofNat total, decide (wordBase ≤ total))

/--
Subtract two words with an incoming borrow bit, returning the low word and
the outgoing borrow bit.
-/
def subBorrow (a b : UInt64) (bin : Bool) : UInt64 × Bool :=
  let rhs := b.toNat + bin.toNat
  if a.toNat < rhs then
    (.ofNat (wordBase + a.toNat - rhs), true)
  else
    (.ofNat (a.toNat - rhs), false)

/-- `mulHi` computes the natural-number quotient of the full product by `2^64`. -/
theorem toNat_mulHi (a b : UInt64) :
    (mulHi a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  sorry

/-- High and low product words reconstruct the full natural-number product. -/
theorem mulHi_mulLo (a b : UInt64) :
    (mulHi a b).toNat * 2 ^ 64 + (a * b).toNat = a.toNat * b.toNat := by
  sorry

/-- `addCarry` splits the full sum into a low word and an outgoing carry bit. -/
theorem toNat_addCarry (a b : UInt64) (cin : Bool) :
    let (s, cout) := addCarry a b cin
    s.toNat + cout.toNat * 2 ^ 64 = a.toNat + b.toNat + cin.toNat := by
  sorry

end UInt64
