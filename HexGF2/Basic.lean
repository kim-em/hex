import Std

/-!
Core packed polynomial definitions for `hex-gf2`.

This module models polynomials over `F_2` as arrays of `UInt64` words in
ascending degree order. It provides normalization, degree/bit accessors,
word-wise XOR addition, and shifts by powers of `x`.
-/
namespace Hex

/-- Packed-word normalization for `GF2Poly`: either the polynomial is zero, or
its highest stored word is nonzero. -/
def GF2PolyNormalized (words : Array UInt64) : Prop :=
  words.size = 0 ∨ words.back? ≠ some (0 : UInt64)

/-- Polynomials over `F_2`, packed into 64-bit words. Bit `j` of `words[i]`
stores the coefficient of `x^(64 * i + j)`. -/
structure GF2Poly where
  words : Array UInt64
  normalized : GF2PolyNormalized words

namespace GF2Poly

/-- Remove trailing zero words without disturbing the lower-degree prefix. -/
private def trimTrailingZeroWordsList : List UInt64 → List UInt64
  | [] => []
  | w :: ws =>
      let trimmed := trimTrailingZeroWordsList ws
      if trimmed = [] ∧ w = 0 then [] else w :: trimmed

/-- Normalize a word array by discarding trailing zero words. -/
private def normalizeWords (words : Array UInt64) : Array UInt64 :=
  (trimTrailingZeroWordsList words.toList).toArray

/-- The index of the highest set bit in a machine word, if any. -/
private def highestSetBit? (w : UInt64) : Option Nat :=
  (List.range 64).reverse.find? fun i => (((w >>> i.toUInt64) &&& 1) != 0)

/-- Build a normalized packed polynomial from a raw word array. -/
def ofWords (words : Array UInt64) : GF2Poly :=
  let normalizedWords := normalizeWords words
  { words := normalizedWords
    normalized := by
      classical
      sorry }

/-- The zero polynomial. -/
def zero : GF2Poly :=
  ofWords #[]

instance : Zero GF2Poly where
  zero := zero

/-- The constant polynomial `1`. -/
def one : GF2Poly :=
  ofWords #[1]

instance : One GF2Poly where
  one := one

/-- Build a packed polynomial from a single machine word. -/
def ofUInt64 (w : UInt64) : GF2Poly :=
  ofWords #[w]

/-- The monomial `x^n`. -/
def monomial (n : Nat) : GF2Poly :=
  let wordIdx := n / 64
  let bitIdx := n % 64
  ofWords <| (Array.replicate wordIdx (0 : UInt64)).push ((1 : UInt64) <<< bitIdx.toUInt64)

/-- The stored packed words. -/
def toWords (p : GF2Poly) : Array UInt64 :=
  p.words

/-- Number of stored machine words. -/
def wordCount (p : GF2Poly) : Nat :=
  p.words.size

/-- `true` exactly when the polynomial is zero. -/
def isZero (p : GF2Poly) : Bool :=
  p.words.isEmpty

/-- Proposition-level zero predicate used by the packed quotient wrappers. -/
def IsZero (p : GF2Poly) : Prop :=
  p.isZero = true

/-- The coefficient of `x^n`. -/
def coeff (p : GF2Poly) (n : Nat) : Bool :=
  let word := p.words.getD (n / 64) 0
  (((word >>> (n % 64).toUInt64) &&& 1) != 0)

/-- The degree of a nonzero polynomial, if any. -/
def degree? (p : GF2Poly) : Option Nat :=
  match p.words.back? with
  | none => none
  | some last =>
      match highestSetBit? last with
      | none => none
      | some bitIdx => some (64 * (p.words.size - 1) + bitIdx)

/-- The degree of a polynomial, defaulting to `0` for the zero polynomial. -/
def degree (p : GF2Poly) : Nat :=
  p.degree?.getD 0

/-- Word-wise XOR of packed coefficient arrays. -/
private def xorWords (xs ys : Array UInt64) : Array UInt64 :=
  Array.ofFn fun i : Fin (max xs.size ys.size) => xs.getD i.1 0 ^^^ ys.getD i.1 0

/-- Addition in `F_2[x]` is coefficientwise XOR. -/
def add (p q : GF2Poly) : GF2Poly :=
  ofWords (xorWords p.words q.words)

instance : Add GF2Poly where
  add := add

/-- Shift a normalized word list left by `bitShift ∈ [1, 63]`. -/
private def shiftLeftBitsList (bitShift : Nat) (carry : UInt64) : List UInt64 → List UInt64
  | [] =>
      if carry = 0 then [] else [carry]
  | w :: ws =>
      let out := (w <<< bitShift.toUInt64) ||| carry
      let nextCarry := w >>> (64 - bitShift).toUInt64
      out :: shiftLeftBitsList bitShift nextCarry ws

/-- Shift packed words right by `bitShift ∈ [1, 63]`, reading the input from
high degree to low degree. -/
private def shiftRightBitsRevList (bitShift : Nat) (carry : UInt64) :
    List UInt64 → List UInt64
  | [] => []
  | w :: ws =>
      let out := (w >>> bitShift.toUInt64) ||| carry
      let nextCarry := w <<< (64 - bitShift).toUInt64
      out :: shiftRightBitsRevList bitShift nextCarry ws

/-- Multiply by `x^k`. -/
def shiftLeft (p : GF2Poly) (k : Nat) : GF2Poly :=
  let wordShift := k / 64
  let bitShift := k % 64
  let shiftedBits :=
    if bitShift = 0 then
      p.words
    else
      (shiftLeftBitsList bitShift 0 p.words.toList).toArray
  ofWords <| (Array.replicate wordShift (0 : UInt64)) ++ shiftedBits

/-- Divide by `x^k`, discarding the remainder. -/
def shiftRight (p : GF2Poly) (k : Nat) : GF2Poly :=
  let wordShift := k / 64
  let bitShift := k % 64
  let dropped := (p.words.toList.drop wordShift).toArray
  let shiftedBits :=
    if bitShift = 0 then
      dropped
    else
      ((shiftRightBitsRevList bitShift 0 dropped.toList.reverse).reverse).toArray
  ofWords shiftedBits

/-- Alias for multiplication by a power of `x`. -/
def mulXk (p : GF2Poly) (k : Nat) : GF2Poly :=
  shiftLeft p k

/-- Alias for exact division by a power of `x` when the low coefficients vanish;
otherwise this drops the discarded remainder. -/
def divXk (p : GF2Poly) (k : Nat) : GF2Poly :=
  shiftRight p k

end GF2Poly
end Hex
