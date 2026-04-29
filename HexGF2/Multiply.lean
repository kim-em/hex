import HexGF2.Basic
import HexGF2.Clmul

/-!
Packed `GF2Poly` multiplication.

This module lifts the carry-less `UInt64` primitive to polynomial
multiplication on packed `GF(2)` coefficients. Each word pair contributes a
128-bit carry-less product, which is XOR-accumulated into the result words and
then normalized back into the `GF2Poly` invariant.
-/
namespace Hex
namespace GF2Poly

/-- XOR a 128-bit carry-less product into adjacent result words. -/
private def xorClmulAt (acc : Array UInt64) (idx : Nat) (x y : UInt64) : Array UInt64 :=
  let (hi, lo) := clmul x y
  let acc := acc.set! idx (acc[idx]! ^^^ lo)
  acc.set! (idx + 1) (acc[idx + 1]! ^^^ hi)

private theorem xorClmulAt_size (acc : Array UInt64) (idx : Nat) (x y : UInt64) :
    (xorClmulAt acc idx x y).size = acc.size := by
  simp [xorClmulAt]

private theorem foldl_xorClmulAt_size (js : List Nat) (acc : Array UInt64)
    (idx : Nat) (x : UInt64) (ys : Array UInt64) :
    (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc).size = acc.size := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, xorClmulAt_size]

private theorem foldl_mulWords_size (is : List Nat) (acc : Array UInt64)
    (xs ys : Array UInt64) :
    (is.foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range ys.size).foldl
            (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
            acc)
        acc).size = acc.size := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      simp only [List.foldl_cons]
      have hinner := foldl_xorClmulAt_size (List.range ys.size) acc i xs[i]! ys
      rw [ih, hinner]

private theorem bit_eq_one_eq_testBit (x i : Nat) :
    (x >>> i % 2 == 1) = x.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.shiftRight_eq_div_pow]
  apply decide_eq_decide.mpr
  exact Iff.rfl

private theorem UInt64.bit_xor_bne (a b : UInt64) (i : Nat) :
    ((((a ^^^ b) >>> i.toUInt64) &&& 1) != 0) =
      ((((a >>> i.toUInt64) &&& 1) != 0) !=
        (((b >>> i.toUInt64) &&& 1) != 0)) := by
  rw [UInt64.bne_zero_eq_toNat_bne_zero]
  rw [UInt64.bne_zero_eq_toNat_bne_zero]
  rw [UInt64.bne_zero_eq_toNat_bne_zero]
  simp [UInt64.toNat_xor, UInt64.toNat_shiftRight, UInt64.toNat_and]
  rw [bit_eq_one_eq_testBit]
  rw [bit_eq_one_eq_testBit]
  rw [bit_eq_one_eq_testBit]
  simp [Nat.testBit_xor]

private theorem coeffWords_xorClmulAt_low (acc : Array UInt64) {idx n : Nat}
    (x y : UInt64) (hidx : idx < acc.size) (hn : n / 64 = idx) :
    coeffWords (xorClmulAt acc idx x y) n =
      (coeffWords acc n !=
        ((((clmul x y).2 >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  simp [xorClmulAt, coeffWords, hn, hidx, UInt64.bit_xor_bne]

private theorem coeffWords_xorClmulAt_high (acc : Array UInt64) {idx n : Nat}
    (x y : UInt64) (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hn : n / 64 = idx + 1) :
    coeffWords (xorClmulAt acc idx x y) n =
      (coeffWords acc n !=
        ((((clmul x y).1 >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  simp [xorClmulAt, coeffWords, hn, hidx, hidxNext, UInt64.bit_xor_bne]

private theorem coeffWords_xorClmulAt_ne (acc : Array UInt64) {idx n : Nat}
    (x y : UInt64) (hnLow : n / 64 ≠ idx) (hnHigh : n / 64 ≠ idx + 1) :
    coeffWords (xorClmulAt acc idx x y) n = coeffWords acc n := by
  have hLow : idx ≠ n / 64 := Ne.symm hnLow
  have hHigh : idx + 1 ≠ n / 64 := Ne.symm hnHigh
  simp [xorClmulAt, coeffWords, hLow, hHigh]

private theorem foldl_keep {α β : Type} (xs : List β) (acc : α) :
    xs.foldl (fun acc _ => acc) acc = acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons _ xs ih => simp [ih]

private theorem clmul_zero_right (x : UInt64) : clmul x 0 = (0, 0) := by
  simp [clmul, pureClmul, foldl_keep]

private theorem Array.setIfInBounds_getElem! (xs : Array UInt64) (idx : Nat) :
    xs.setIfInBounds idx xs[idx]! = xs := by
  unfold Array.setIfInBounds
  by_cases h : idx < xs.size
  · simp [h]
  · simp [h]

private theorem xorClmulAt_zero_right (acc : Array UInt64) (idx : Nat) (x : UInt64) :
    xorClmulAt acc idx x 0 = acc := by
  simp [xorClmulAt, clmul_zero_right, Array.setIfInBounds_getElem!]

private theorem coeffWords_xorClmulAt_zero_right (acc : Array UInt64) (idx n : Nat)
    (x : UInt64) :
    coeffWords (xorClmulAt acc idx x 0) n = coeffWords acc n := by
  rw [xorClmulAt_zero_right]

private theorem foldl_xorClmulAt_zero_right_coeff (js : List Nat) (acc : Array UInt64)
    (idx n : Nat) (x : UInt64) (ys : Array UInt64)
    (hzero : ∀ j ∈ js, ys[j]! = 0) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc)
        n =
      coeffWords acc n := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      have hjzero : ys[j]! = 0 := hzero j (by simp)
      have htail : ∀ j' ∈ js, ys[j']! = 0 := by
        intro j' hj'
        exact hzero j' (by simp [hj'])
      simp only [List.foldl_cons]
      rw [hjzero, ih (acc := xorClmulAt acc (idx + j) x 0) htail,
        coeffWords_xorClmulAt_zero_right]

/-- Raw packed-word multiplication before trailing zero normalization. -/
private def mulWords (xs ys : Array UInt64) : Array UInt64 :=
  if xs.isEmpty || ys.isEmpty then
    #[]
  else
    (List.range xs.size).foldl
      (fun acc i =>
        let x := xs[i]!
        (List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
          acc)
      (Array.replicate (xs.size + ys.size) (0 : UInt64))

/-- Multiplication in `F_2[x]` via carry-less word products and XOR
accumulation. -/
def mul (p q : GF2Poly) : GF2Poly :=
  ofWords (mulWords p.words q.words)

instance : Mul GF2Poly where
  mul := mul

@[simp] theorem zero_mul (p : GF2Poly) : (0 : GF2Poly) * p = 0 := by
  apply ext_words
  change (mul 0 p).words = #[]
  simp [mul, mulWords]

@[simp] theorem mul_zero (p : GF2Poly) : p * (0 : GF2Poly) = 0 := by
  apply ext_words
  change (mul p 0).words = #[]
  simp [mul, mulWords]

/-- The normalized product stores no more than the raw convolution capacity. -/
theorem wordCount_mul_le (p q : GF2Poly) : (p * q).wordCount ≤ p.wordCount + q.wordCount := by
  have hnorm := normalizeWords_size_le (mulWords p.words q.words)
  have hraw : (mulWords p.words q.words).size ≤ p.wordCount + q.wordCount := by
    unfold mulWords GF2Poly.wordCount
    by_cases hxs : p.words.isEmpty <;> by_cases hys : q.words.isEmpty
    · simp [hxs, hys]
    · simp [hxs, hys]
    · simp [hxs, hys]
    · simp [hxs, hys, foldl_mulWords_size]
  calc
    (p * q).wordCount = (ofWords (mulWords p.words q.words)).words.size := by
      rfl
    _ ≤ (mulWords p.words q.words).size := hnorm
    _ ≤ p.wordCount + q.wordCount := hraw

/-- Multiplication by a monomial has the expected packed-word capacity bound. -/
theorem wordCount_mul_monomial_le (p : GF2Poly) (k : Nat) :
    (p * monomial k).wordCount ≤ p.wordCount + (k / 64 + 1) := by
  exact Nat.le_trans (wordCount_mul_le p (monomial k))
    (Nat.add_le_add_left (wordCount_monomial_le k) p.wordCount)

/-- Multiplication coefficients reduce to the raw carry-less word product. -/
theorem coeff_mul (p q : GF2Poly) (n : Nat) :
    (p * q).coeff n = coeffWords (mulWords p.words q.words) n := by
  change (ofWords (mulWords p.words q.words)).coeff n =
    coeffWords (mulWords p.words q.words) n
  simp

end GF2Poly
end Hex
