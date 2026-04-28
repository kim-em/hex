import HexArith.ExtGcd
import HexArith.UInt64.Wide

/-!
Core conformance checks for the first `hex-arith` Phase 3 slice.

Oracle: Lean built-in `Nat` / `Int` arithmetic
Mode: always
Covered operations:
- `HexArith.extGcd` on `Nat`
- `HexArith.Int.extGcd`
- `HexArith.UInt64.extGcd`
- `UInt64.mulHi`
- `UInt64.mulFull`
- `UInt64.addCarry`
- `UInt64.subBorrow`
Covered properties:
- each extended-GCD API returns the same gcd as Lean's built-in arithmetic on committed fixtures
- each extended-GCD API returns Bezout coefficients satisfying the advertised identity
- `mulHi` and `mulFull` reconstruct the committed Nat-level products
- `addCarry` and `subBorrow` satisfy the committed one-word reconstruction laws
Covered edge cases:
- zero-left and zero-right extended-GCD inputs
- signed extended-GCD inputs with mixed signs
- wide-word products crossing the `2^64` boundary
- add-with-carry and subtract-with-borrow cases with and without overflow
-/

namespace HexArith

private def wordBase : Nat := UInt64.word
private def maxWord : UInt64 := UInt64.ofNat (wordBase - 1)

/-- info: (6, 1, -2) -/
#guard_msgs in #eval HexArith.extGcd 30 12

#guard let (g, _, _) := HexArith.extGcd 30 12
  g = Nat.gcd 30 12
#guard let (g, s, t) := HexArith.extGcd 30 12
  s * 30 + t * 12 = g

#guard let (g, _, _) := HexArith.extGcd 0 37
  g = Nat.gcd 0 37
#guard let (g, s, t) := HexArith.extGcd 0 37
  s * 0 + t * 37 = g

#guard let (g, _, _) := HexArith.extGcd 144 89
  g = Nat.gcd 144 89
#guard let (g, s, t) := HexArith.extGcd 144 89
  s * 144 + t * 89 = g

/-- info: (6, 1, -2) -/
#guard_msgs in #eval HexArith.Int.extGcd 30 12

#guard let (g, _, _) := HexArith.Int.extGcd 30 12
  g = Int.gcd 30 12
#guard let (g, s, t) := HexArith.Int.extGcd 30 12
  s * 30 + t * 12 = Int.ofNat g

#guard let (g, _, _) := HexArith.Int.extGcd 37 0
  g = Int.gcd 37 0
#guard let (g, s, t) := HexArith.Int.extGcd 37 0
  s * 37 + t * 0 = Int.ofNat g

#guard let (g, _, _) := HexArith.Int.extGcd (-144) 89
  g = Int.gcd (-144) 89
#guard let (g, s, t) := HexArith.Int.extGcd (-144) 89
  s * (-144) + t * 89 = Int.ofNat g

/-- info: (6, 1, -2) -/
#guard_msgs in #eval HexArith.UInt64.extGcd 30 12

#guard let (g, _, _) := HexArith.UInt64.extGcd 30 12
  g.toNat = Nat.gcd 30 12
#guard let (g, s, t) := HexArith.UInt64.extGcd 30 12
  s * 30 + t * 12 = Int.ofNat g.toNat

#guard let (g, _, _) := HexArith.UInt64.extGcd 0 37
  g.toNat = Nat.gcd 0 37
#guard let (g, s, t) := HexArith.UInt64.extGcd 0 37
  s * 0 + t * 37 = Int.ofNat g.toNat

#guard let a := UInt64.ofNat (2 ^ 32 + 15)
  let b := UInt64.ofNat (2 ^ 31 - 1)
  let (g, _, _) := HexArith.UInt64.extGcd a b
  g.toNat = Nat.gcd a.toNat b.toNat
#guard let a := UInt64.ofNat (2 ^ 32 + 15)
  let b := UInt64.ofNat (2 ^ 31 - 1)
  let (g, s, t) := HexArith.UInt64.extGcd a b
  s * Int.ofNat a.toNat + t * Int.ofNat b.toNat = Int.ofNat g.toNat

/-- info: 2 -/
#guard_msgs in #eval UInt64.mulHi (UInt64.ofNat (2 ^ 63)) 4

#guard UInt64.mulHi 0 17 = 0
#guard UInt64.mulHi (UInt64.ofNat (2 ^ 63)) 4 = UInt64.ofNat 2
#guard let a := maxWord
  let b := maxWord
  (UInt64.mulHi a b).toNat * wordBase + (a * b).toNat = a.toNat * b.toNat

/-- info: (2, 0) -/
#guard_msgs in #eval UInt64.mulFull (UInt64.ofNat (2 ^ 63)) 4

#guard let (hi, lo) := UInt64.mulFull 0 17
  hi = 0 ∧ lo = 0
#guard let (hi, lo) := UInt64.mulFull (UInt64.ofNat (2 ^ 63)) 4
  hi = UInt64.ofNat 2 ∧ lo = 0
#guard let a := maxWord
  let b := UInt64.ofNat (2 ^ 32 + 1)
  let (hi, lo) := UInt64.mulFull a b
  hi.toNat * wordBase + lo.toNat = a.toNat * b.toNat

/-- info: (0, true) -/
#guard_msgs in #eval UInt64.addCarry maxWord 1 false

#guard let (s, cout) := UInt64.addCarry 0 0 false
  s = 0 ∧ cout = false
#guard let (s, cout) := UInt64.addCarry maxWord 1 false
  s = 0 ∧ cout = true
#guard let (s, cout) := UInt64.addCarry maxWord maxWord true
  s = maxWord ∧ cout = true
#guard let a := UInt64.ofNat (2 ^ 63)
  let b := UInt64.ofNat (2 ^ 63)
  let (s, cout) := UInt64.addCarry a b false
  s.toNat + cout.toNat * wordBase = a.toNat + b.toNat

/-- info: (2, false) -/
#guard_msgs in #eval UInt64.subBorrow 5 3 false

#guard let (d, bout) := UInt64.subBorrow 5 3 false
  d = 2 ∧ bout = false
#guard let (d, bout) := UInt64.subBorrow 0 1 false
  d = maxWord ∧ bout = true
#guard let (d, bout) := UInt64.subBorrow 0 0 true
  d = maxWord ∧ bout = true
#guard let a := UInt64.ofNat (2 ^ 63)
  let b := UInt64.ofNat (2 ^ 63 - 1)
  let (d, bout) := UInt64.subBorrow a b true
  d.toNat + (b.toNat + 1) = a.toNat + bout.toNat * wordBase

end HexArith
