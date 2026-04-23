import HexGF2.Ops

/-!
Packed multiplication scaffolding for `GF(2)` polynomials.

This module adds the Phase 1 multiplication layer for `GF2Poly`: executable
word-array multiplication built from the `clmul` boundary together with the
public polynomial multiplication operation and its initial theorem surface.
-/

namespace HexGF2

namespace GF2Poly

/-- Multiply two packed `GF(2)` words, returning the high and low halves. -/
def mulWord (x y : UInt64) : UInt64 × UInt64 :=
  clmul x y

/-- XOR a word into an array slot. Indices outside the array are ignored. -/
private def xorAt (words : Array UInt64) (idx : Nat) (value : UInt64) : Array UInt64 :=
  if idx < words.size then
    words.set! idx (words[idx]! ^^^ value)
  else
    words

/--
Schoolbook multiplication on packed word arrays.

Each 64-bit block product is computed with carry-less multiplication and
accumulated with XOR, matching convolution over `GF(2)`.
-/
def mulWords (xs ys : Array UInt64) : Array UInt64 := Id.run do
  if xs.isEmpty || ys.isEmpty then
    pure #[]
  else
    let outSize := xs.size + ys.size
    let mut out : Array UInt64 := (List.replicate outSize (0 : UInt64)).toArray
    for i in List.range xs.size do
      for j in List.range ys.size do
        let (hi, lo) := mulWord xs[i]! ys[j]!
        let idx := i + j
        out := xorAt out idx lo
        out := xorAt out (idx + 1) hi
    pure out

/-- Packed polynomial multiplication reduces normalized word-array multiplication. -/
def mul (f g : GF2Poly) : GF2Poly :=
  ofWords (mulWords f.words g.words)

/-- Packed `GF(2)` polynomials multiply via normalized `mulWords`. -/
instance : Mul GF2Poly where
  mul := mul

/-- Carry-less block multiplication is definitionally `clmul`. -/
theorem mulWord_eq_clmul (x y : UInt64) :
    mulWord x y = clmul x y := by
  rfl

/-- Packed multiplication is definitionally normalized `mulWords`. -/
theorem mul_eq_ofWords (f g : GF2Poly) :
    f * g = ofWords (mulWords f.words g.words) := by
  rfl

/-- Empty packed words annihilate multiplication on the left. -/
theorem mulWords_nil_left (ys : Array UInt64) :
    mulWords #[] ys = #[] := by
  simp [mulWords]

/-- Empty packed words annihilate multiplication on the right. -/
theorem mulWords_nil_right (xs : Array UInt64) :
    mulWords xs #[] = #[] := by
  by_cases h : xs.isEmpty
  · simp [mulWords, h]
  · simp [mulWords, h]

/-- Packed `GF(2)` multiplication is commutative. -/
theorem mul_comm (f g : GF2Poly) : f * g = g * f := by
  sorry

/-- Multiplying on the left by the zero packed polynomial yields zero. -/
theorem zero_mul (f : GF2Poly) :
    ofWords #[] * f = ofWords #[] := by
  sorry

/-- Multiplying on the right by the zero packed polynomial yields zero. -/
theorem mul_zero (f : GF2Poly) :
    f * ofWords #[] = ofWords #[] := by
  sorry

end GF2Poly

end HexGF2
