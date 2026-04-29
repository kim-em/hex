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

/-- Packed polynomials are equal when their normalized word arrays are equal. -/
theorem ext_words {p q : GF2Poly} (h : p.words = q.words) : p = q := by
  cases p
  cases q
  simp at h
  subst h
  simp

/-- Remove trailing zero words without disturbing the lower-degree prefix. -/
private def trimTrailingZeroWordsList : List UInt64 → List UInt64
  | [] => []
  | w :: ws =>
      let trimmed := trimTrailingZeroWordsList ws
      if trimmed = [] ∧ w = 0 then [] else w :: trimmed

private theorem trimTrailingZeroWordsList_getLast?_ne_zero :
    ∀ ws : List UInt64,
      let trimmed := trimTrailingZeroWordsList ws
      trimmed = [] ∨ trimmed.getLast? ≠ some (0 : UInt64)
  | [] => by simp [trimTrailingZeroWordsList]
  | w :: ws => by
      dsimp
      have htrim := trimTrailingZeroWordsList_getLast?_ne_zero ws
      by_cases hdrop : trimTrailingZeroWordsList ws = [] ∧ w = 0
      · simp [trimTrailingZeroWordsList, hdrop]
      · by_cases hnil : trimTrailingZeroWordsList ws = []
        · have hw : w ≠ 0 := by
            intro hw0
            apply hdrop
            exact ⟨hnil, hw0⟩
          simp [trimTrailingZeroWordsList, hnil, hw]
        · have hlast : (trimTrailingZeroWordsList ws).getLast? ≠ some (0 : UInt64) := by
            cases htrim with
            | inl h =>
                contradiction
            | inr h =>
                exact h
          cases hrest : trimTrailingZeroWordsList ws with
          | nil =>
              contradiction
          | cons x xs =>
              simpa [trimTrailingZeroWordsList, hdrop, hrest] using hlast

private theorem trimTrailingZeroWordsList_length_le (ws : List UInt64) :
    (trimTrailingZeroWordsList ws).length ≤ ws.length := by
  induction ws with
  | nil =>
      simp [trimTrailingZeroWordsList]
  | cons w ws ih =>
      by_cases hdrop : trimTrailingZeroWordsList ws = [] ∧ w = 0
      · have hnil : trimTrailingZeroWordsList (w :: ws) = [] := by
          simp [trimTrailingZeroWordsList, hdrop]
        rw [hnil]
        exact Nat.zero_le _
      · have hcons : trimTrailingZeroWordsList (w :: ws) = w :: trimTrailingZeroWordsList ws := by
          simp [trimTrailingZeroWordsList, hdrop]
        rw [hcons]
        simp [ih]

private theorem trimTrailingZeroWordsList_getD (ws : List UInt64) (i : Nat) :
    (trimTrailingZeroWordsList ws).getD i 0 = ws.getD i 0 := by
  induction ws generalizing i with
  | nil =>
      simp [trimTrailingZeroWordsList]
  | cons w ws ih =>
      by_cases hdrop : trimTrailingZeroWordsList ws = [] ∧ w = 0
      · cases i with
        | zero =>
            simp [trimTrailingZeroWordsList, hdrop]
        | succ i =>
            have htail : ws.getD i 0 = 0 := by
              rw [← ih i, hdrop.1]
              simp
            simpa [trimTrailingZeroWordsList, hdrop, List.getD] using htail.symm
      · cases i with
        | zero =>
            simp [trimTrailingZeroWordsList, hdrop]
        | succ i =>
            simpa [trimTrailingZeroWordsList, hdrop, List.getD] using ih i

/-- Normalize a word array by discarding trailing zero words. -/
def normalizeWords (words : Array UInt64) : Array UInt64 :=
  (trimTrailingZeroWordsList words.toList).toArray

/-- Packed-word coefficient lookup before wrapping the array as a `GF2Poly`. -/
def coeffWords (words : Array UInt64) (n : Nat) : Bool :=
  let word := words[n / 64]?.getD 0
  (((word >>> (n % 64).toUInt64) &&& 1) != 0)

/-- Trailing-zero normalization preserves every packed coefficient word. -/
theorem normalizeWords_get?_getD (words : Array UInt64) (i : Nat) :
    ((normalizeWords words)[i]?).getD 0 = (words[i]?).getD 0 := by
  simpa [normalizeWords, Array.getD, List.getD] using
    trimTrailingZeroWordsList_getD words.toList i

/-- Trailing-zero normalization preserves packed coefficients. -/
theorem coeffWords_normalizeWords (words : Array UInt64) (n : Nat) :
    coeffWords (normalizeWords words) n = coeffWords words n := by
  rw [coeffWords, coeffWords, normalizeWords_get?_getD]

/-- The index of the highest set bit in a machine word, if any. -/
private def highestSetBit? (w : UInt64) : Option Nat :=
  (List.range 64).reverse.find? fun i => (((w >>> i.toUInt64) &&& 1) != 0)

/-- Build a normalized packed polynomial from a raw word array. -/
def ofWords (words : Array UInt64) : GF2Poly :=
  let normalizedWords := normalizeWords words
  { words := normalizedWords
    normalized := by
      classical
      simpa [normalizedWords, normalizeWords, GF2PolyNormalized] using
        trimTrailingZeroWordsList_getLast?_ne_zero words.toList }

@[simp] theorem words_ofWords_empty : (ofWords #[]).words = #[] := by
  rfl

/-- The zero polynomial. -/
def zero : GF2Poly :=
  ofWords #[]

instance : Zero GF2Poly where
  zero := zero

@[simp] theorem ofWords_empty : ofWords #[] = 0 := by
  apply ext_words
  rfl

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
  coeffWords p.words n

/-- Coefficients of a raw word array are unchanged by `ofWords` normalization. -/
@[simp] theorem coeff_ofWords (words : Array UInt64) (n : Nat) :
    (ofWords words).coeff n = coeffWords words n := by
  simp [ofWords, coeff, coeffWords_normalizeWords]

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

@[simp] theorem words_zero : (0 : GF2Poly).words = #[] := by
  rfl

@[simp] theorem wordCount_zero : (0 : GF2Poly).wordCount = 0 := by
  rfl

@[simp] theorem isZero_zero : (0 : GF2Poly).isZero = true := by
  rfl

@[simp] theorem coeff_zero (n : Nat) : (0 : GF2Poly).coeff n = false := by
  simp [coeff, coeffWords]

@[simp] theorem degree?_zero : (0 : GF2Poly).degree? = none := by
  rfl

@[simp] theorem degree_zero : (0 : GF2Poly).degree = 0 := by
  rfl

/-- Word-wise XOR of packed coefficient arrays. -/
def xorWords (xs ys : Array UInt64) : Array UInt64 :=
  Array.ofFn fun i : Fin (max xs.size ys.size) => xs.getD i.1 0 ^^^ ys.getD i.1 0

/-- Addition in `F_2[x]` is coefficientwise XOR. -/
def add (p q : GF2Poly) : GF2Poly :=
  ofWords (xorWords p.words q.words)

instance : Add GF2Poly where
  add := add

/-- Addition coefficients are the normalized packed XOR of the input words. -/
theorem coeff_add (p q : GF2Poly) (n : Nat) :
    (p + q).coeff n = coeffWords (xorWords p.words q.words) n := by
  change (add p q).coeff n = coeffWords (xorWords p.words q.words) n
  simp [add]

/-- Shift a normalized word list left by `bitShift ∈ [1, 63]`. -/
def shiftLeftBitsList (bitShift : Nat) (carry : UInt64) : List UInt64 → List UInt64
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

/-- Monomial coefficients reduce to the coefficient lookup on its packed word array. -/
theorem coeff_monomial (n m : Nat) :
    (monomial n).coeff m =
      coeffWords
        ((Array.replicate (n / 64) (0 : UInt64)).push ((1 : UInt64) <<< (n % 64).toUInt64))
        m := by
  simp [monomial]

/-- Shift-left coefficients reduce to the coefficient lookup on the shifted packed words. -/
theorem coeff_shiftLeft (p : GF2Poly) (k n : Nat) :
    (p.shiftLeft k).coeff n =
      coeffWords
        ((Array.replicate (k / 64) (0 : UInt64)) ++
          if k % 64 = 0 then
            p.words
          else
            (shiftLeftBitsList (k % 64) 0 p.words.toList).toArray)
        n := by
  simp [shiftLeft]

/-- `mulXk` is coefficientwise the same as `shiftLeft`. -/
theorem coeff_mulXk (p : GF2Poly) (k n : Nat) :
    (p.mulXk k).coeff n = (p.shiftLeft k).coeff n := by
  rfl

/-- Alias for exact division by a power of `x` when the low coefficients vanish;
otherwise this drops the discarded remainder. -/
def divXk (p : GF2Poly) (k : Nat) : GF2Poly :=
  shiftRight p k

/-- Normalization never increases the number of stored machine words. -/
theorem normalizeWords_size_le (words : Array UInt64) :
    (normalizeWords words).size ≤ words.size := by
  simpa [normalizeWords] using trimTrailingZeroWordsList_length_le words.toList

/-- Wrapping raw words never increases the stored word count. -/
theorem wordCount_ofWords_le (words : Array UInt64) :
    (ofWords words).wordCount ≤ words.size := by
  exact normalizeWords_size_le words

/-- Addition stores no more words than the larger input. -/
theorem wordCount_add_le (p q : GF2Poly) :
    (p + q).wordCount ≤ max p.wordCount q.wordCount := by
  calc
    (p + q).wordCount = (ofWords (xorWords p.words q.words)).wordCount := by
      rfl
    _ ≤ (xorWords p.words q.words).size := wordCount_ofWords_le _
    _ = max p.wordCount q.wordCount := by
      simp [xorWords, wordCount]

/-- The monomial `x^n` stores at most the one word containing its bit. -/
theorem wordCount_monomial_le (n : Nat) :
    (monomial n).wordCount ≤ n / 64 + 1 := by
  calc
    (monomial n).wordCount
        ≤ ((Array.replicate (n / 64) (0 : UInt64)).push
            ((1 : UInt64) <<< (n % 64).toUInt64)).size := by
          exact wordCount_ofWords_le _
    _ = n / 64 + 1 := by
      simp

end GF2Poly
end Hex
