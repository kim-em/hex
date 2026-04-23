import HexGF2.FiniteExtension

/-!
Executable packed-polynomial operations for `GF(2)`.

This module adds the first arithmetic layer for `GF2Poly`: normalization of
packed words, wordwise XOR addition, and shifts corresponding to
multiplication or division by `x^k`.
-/

namespace HexGF2

namespace GF2Poly

/-- Remove trailing zero words while preserving the represented polynomial. -/
private def normalizeWordList : List UInt64 → List UInt64
  | [] => []
  | w :: ws =>
      let tail := normalizeWordList ws
      match tail with
      | [] => if w = 0 then [] else [w]
      | _ => w :: tail

/-- Drop trailing zero words from a packed `GF(2)` polynomial representation. -/
def normalizeWords (words : Array UInt64) : Array UInt64 :=
  (normalizeWordList words.toList).toArray

/-- The largest set bit in a word, if the word is nonzero. -/
def highestBit? (word : UInt64) : Option Nat := Id.run do
  let mut result : Option Nat := none
  for i in List.range 64 do
    let mask := (1 : UInt64) <<< (UInt64.ofNat i)
    if word &&& mask != 0 then
      result := some i
  pure result

/-- Build a packed polynomial from raw words by normalizing trailing zeros. -/
def ofWords (words : Array UInt64) : GF2Poly :=
  let normalized := normalizeWords words
  match h : normalized.back? with
  | none =>
      { words := #[]
        degree := 0
        wf := by
          left
          simp }
  | some last =>
      let bit := highestBit? last |>.getD 0
      let degree := 64 * (normalized.size - 1) + bit
      { words := normalized
        degree := degree
        wf := by
          right
          sorry }

/-- XOR the stored packed words of two `GF(2)` polynomials. -/
def xorWords (xs ys : Array UInt64) : Array UInt64 := Id.run do
  let size := max xs.size ys.size
  let mut out : Array UInt64 := #[]
  for i in List.range size do
    out := out.push (xs.getD i 0 ^^^ ys.getD i 0)
  pure out

/-- Shift packed words left by whole words and residual bits. -/
def shiftLeftWords (words : Array UInt64) (k : Nat) : Array UInt64 := Id.run do
  if words.isEmpty then
    pure #[]
  else
    let wordShift := k / 64
    let bitShift := k % 64
    let extra := if bitShift = 0 then 0 else 1
    let mut out : Array UInt64 :=
      (List.replicate (words.size + wordShift + extra) (0 : UInt64)).toArray
    for i in List.range words.size do
      let word := words[i]!
      let target := i + wordShift
      let current := out[target]!
      out := out.set! target (current ^^^ (word <<< (UInt64.ofNat bitShift)))
      if bitShift = 0 then
        pure ()
      else
        let carryIdx := target + 1
        let carry := word >>> (UInt64.ofNat (64 - bitShift))
        let currentCarry := out[carryIdx]!
        out := out.set! carryIdx (currentCarry ^^^ carry)
    pure out

/-- Shift packed words right by whole words and residual bits. -/
def shiftRightWords (words : Array UInt64) (k : Nat) : Array UInt64 := Id.run do
  let wordShift := k / 64
  let bitShift := k % 64
  if words.size <= wordShift then
    pure #[]
  else
    let outSize := words.size - wordShift
    let mut out : Array UInt64 := #[]
    for i in List.range outSize do
      let source := i + wordShift
      let low := words[source]! >>> (UInt64.ofNat bitShift)
      let high :=
        if bitShift = 0 then
          0
        else if source + 1 < words.size then
          words[source + 1]! <<< (UInt64.ofNat (64 - bitShift))
        else
          0
      out := out.push (low ^^^ high)
    pure out

/-- Packed polynomial addition is wordwise XOR. -/
instance : Add GF2Poly where
  add f g := ofWords (xorWords f.words g.words)

/-- Multiplication by `x^k` shifts the packed representation left by `k` bits. -/
def shiftLeft (f : GF2Poly) (k : Nat) : GF2Poly :=
  ofWords (shiftLeftWords f.words k)

/-- Division by `x^k`, discarding low coefficients, shifts right by `k` bits. -/
def shiftRight (f : GF2Poly) (k : Nat) : GF2Poly :=
  ofWords (shiftRightWords f.words k)

/-- Zero packed words are already normalized. -/
theorem normalizeWords_nil :
    normalizeWords #[] = #[] := by
  rfl

/-- Addition is definitionally the normalized XOR of packed words. -/
theorem add_eq_ofWords (f g : GF2Poly) :
    f + g = ofWords (xorWords f.words g.words) := by
  rfl

/-- Left shift is definitionally normalization after shifting packed words. -/
theorem shiftLeft_eq_ofWords (f : GF2Poly) (k : Nat) :
    shiftLeft f k = ofWords (shiftLeftWords f.words k) := by
  rfl

/-- Right shift is definitionally normalization after shifting packed words. -/
theorem shiftRight_eq_ofWords (f : GF2Poly) (k : Nat) :
    shiftRight f k = ofWords (shiftRightWords f.words k) := by
  rfl

/-- Packed `GF(2)` addition is commutative. -/
theorem add_comm (f g : GF2Poly) : f + g = g + f := by
  sorry

/-- Shifting by zero preserves the packed polynomial. -/
theorem shiftLeft_zero (f : GF2Poly) : shiftLeft f 0 = f := by
  sorry

/-- Right-shifting by zero preserves the packed polynomial. -/
theorem shiftRight_zero (f : GF2Poly) : shiftRight f 0 = f := by
  sorry

end GF2Poly

end HexGF2
