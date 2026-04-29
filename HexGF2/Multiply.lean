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

private theorem clmul_oneHot_low_bit_same_word (x : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hold : old < 64)
    (hbit : old + shift < 64) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).2 >>>
        (old + shift).toUInt64) &&& 1) != 0) =
      (((x >>> old.toUInt64) &&& 1) != 0) := by
  rw [clmul_oneHot_snd x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt hold, Nat.mod_eq_of_lt hbit, bit_eq_one_eq_testBit]
  change (((x.toNat <<< shift) % 18446744073709551616).testBit (old + shift)) =
    x.toNat.testBit old
  rw [show 18446744073709551616 = 2 ^ 64 by rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp [hbit]

private theorem clmul_oneHot_low_bit_before_shift_false (x : UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hbit : bit < shift) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).2 >>>
        bit.toUInt64) &&& 1) != 0) = false := by
  rw [clmul_oneHot_snd x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  have hbit64 : bit < 64 := by omega
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt hbit64, bit_eq_one_eq_testBit]
  change (((x.toNat <<< shift) % 18446744073709551616).testBit bit) = false
  rw [show 18446744073709551616 = 2 ^ 64 by rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp
  intro _ hle
  omega

private theorem clmul_oneHot_low_bit_shifted (x : UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hbit : bit < 64)
    (hle : shift ≤ bit) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).2 >>>
        bit.toUInt64) &&& 1) != 0) =
      (((x >>> (bit - shift).toUInt64) &&& 1) != 0) := by
  have hsource : bit - shift < 64 := by omega
  have hsourceShift : bit - shift + shift < 64 := by omega
  have hsum : bit - shift + shift = bit := by omega
  simpa [hsum] using
    clmul_oneHot_low_bit_same_word x hshiftPos hshift hsource hsourceShift

private theorem clmul_oneHot_high_bit_carry_word (x : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hold : old < 64)
    (hbit : 64 ≤ old + shift) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).1 >>>
        (old + shift - 64).toUInt64) &&& 1) != 0) =
      (((x >>> old.toUInt64) &&& 1) != 0) := by
  have htargetLt : old + shift - 64 < 64 := by omega
  have hshiftCompl : 64 - shift < 64 := by omega
  rw [clmul_oneHot_fst x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  have hold_eq : 64 - shift + (old + shift - 64) = old := by omega
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftRight,
    UInt64.toNat_and, Nat.mod_eq_of_lt hshiftCompl, Nat.mod_eq_of_lt hold,
    Nat.mod_eq_of_lt htargetLt, bit_eq_one_eq_testBit, Nat.testBit_shiftRight,
    hold_eq]

private theorem clmul_oneHot_high_bit_after_carry_false (x : UInt64) {shift bit : Nat}
    (hshift : shift < 64) (hbit : bit < 64) (hle : shift ≤ bit) :
    ((((clmul x ((1 : UInt64) <<< shift.toUInt64)).1 >>>
        bit.toUInt64) &&& 1) != 0) = false := by
  rw [clmul_oneHot_fst x hshift]
  by_cases hshiftZero : shift = 0
  · simp [hshiftZero]
  · simp [hshiftZero, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftRight,
      UInt64.toNat_and, Nat.mod_eq_of_lt (by omega : 64 - shift < 64),
      Nat.mod_eq_of_lt hbit,
      bit_eq_one_eq_testBit, Nat.testBit_shiftRight]
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hxlt : x.toNat < 2 ^ 64 := by
      simpa [UInt64.size, show (18446744073709551616 : Nat) = 2 ^ 64 by rfl]
        using UInt64.toNat_lt_size x
    have hexp : 64 ≤ 64 - shift + bit := by omega
    rw [Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hxlt
        (Nat.pow_le_pow_right (by decide : 0 < 2) hexp))]
    simp

private theorem coeffWords_xorClmulAt_oneHot_low_same_word
    (acc : Array UInt64) {idx n shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : n / 64 = idx) (hbit : n % 64 + shift < 64) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) (n + shift) =
      (coeffWords acc (n + shift) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hold : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetDiv : (n + shift) / 64 = idx := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  have htargetMod : (n + shift) % 64 = n % 64 + shift := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [coeffWords_xorClmulAt_low acc x ((1 : UInt64) <<< shift.toUInt64) hidx
    htargetDiv]
  rw [htargetMod]
  rw [clmul_oneHot_low_bit_same_word x hshiftPos hshift hold hbit]

private theorem coeffWords_xorClmulAt_oneHot_low_before_shift
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : target / 64 = idx) (hbit : target % 64 < shift) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) target =
      coeffWords acc target := by
  rw [coeffWords_xorClmulAt_low acc x ((1 : UInt64) <<< shift.toUInt64) hidx hn]
  rw [clmul_oneHot_low_bit_before_shift_false x hshiftPos hshift hbit]
  simp

private theorem coeffWords_xorClmulAt_oneHot_high_carry_word
    (acc : Array UInt64) {idx n shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : n / 64 = idx) (hbit : 64 ≤ n % 64 + shift) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) (n + shift) =
      (coeffWords acc (n + shift) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hold : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetDiv : (n + shift) / 64 = idx + 1 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  have htargetMod : (n + shift) % 64 = n % 64 + shift - 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [coeffWords_xorClmulAt_high acc x ((1 : UInt64) <<< shift.toUInt64) hidx
    hidxNext htargetDiv]
  rw [htargetMod]
  rw [clmul_oneHot_high_bit_carry_word x hshiftPos hshift hold hbit]

private theorem coeffWords_xorClmulAt_oneHot_high_after_carry
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hshift : shift < 64) (hn : target / 64 = idx + 1)
    (hbit : shift ≤ target % 64) :
    coeffWords (xorClmulAt acc idx x ((1 : UInt64) <<< shift.toUInt64)) target =
      coeffWords acc target := by
  have htargetBit : target % 64 < 64 := Nat.mod_lt target (by decide : 0 < 64)
  rw [coeffWords_xorClmulAt_high acc x ((1 : UInt64) <<< shift.toUInt64) hidx
    hidxNext hn]
  rw [clmul_oneHot_high_bit_after_carry_false x hshift htargetBit hbit]
  simp

private theorem words_monomial_getElem!_active (k : Nat) :
    (monomial k).words[k / 64]! =
      ((1 : UInt64) <<< (k % 64).toUInt64) := by
  rw [words_monomial]
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos (by simp)]
  change ((Array.replicate (k / 64) (0 : UInt64)).push
    ((1 : UInt64) <<< (k % 64).toUInt64))[k / 64] =
      ((1 : UInt64) <<< (k % 64).toUInt64)
  rw [Array.getElem_push]
  simp

private theorem words_monomial_getElem!_zero_lt {j k : Nat} (hj : j < k / 64) :
    (monomial k).words[j]! = 0 := by
  rw [words_monomial]
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos]
  · simp [Array.getElem_push, hj]
  · simp
    omega

private theorem coeffWords_xorClmulAt_monomial_active_low
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  have htarget : n + k = (n + k / 64 * 64) + k % 64 := by
    have hk := Nat.div_add_mod k 64
    omega
  have hsourceMod : (n + k / 64 * 64) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [words_monomial_getElem!_active k, htarget]
  simpa [hsourceMod] using
    coeffWords_xorClmulAt_oneHot_low_same_word
      (acc := acc) (idx := i + k / 64) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

private theorem coeffWords_xorClmulAt_monomial_active_low_before_shift
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hword : target / 64 = i + k / 64)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        target =
      coeffWords acc target := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_low_before_shift
    (acc := acc) (idx := i + k / 64) (target := target)
    (shift := k % 64) x hidx hshiftPos hshift hword hbit

private theorem coeffWords_xorClmulAt_monomial_active_high
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hn : n / 64 = i) (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hshiftPos : 0 < k % 64 := by
    have hnbit : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
    omega
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  have htarget : n + k = (n + k / 64 * 64) + k % 64 := by
    have hk := Nat.div_add_mod k 64
    omega
  have hsourceMod : (n + k / 64 * 64) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [words_monomial_getElem!_active k, htarget]
  simpa [hsourceMod] using
    coeffWords_xorClmulAt_oneHot_high_carry_word
      (acc := acc) (idx := i + k / 64) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hidxNext hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

private theorem coeffWords_xorClmulAt_monomial_active_high_after_carry
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hword : target / 64 = i + k / 64 + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        target =
      coeffWords acc target := by
  have htargetBit : target % 64 < 64 := Nat.mod_lt target (by decide : 0 < 64)
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_high_after_carry
    (acc := acc) (idx := i + k / 64) (target := target)
    (shift := k % 64) x hidx hidxNext hshift hword hbit

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

private theorem foldl_xorClmulAt_monomial_zero_prefix_coeff
    (acc : Array UInt64) (idx n : Nat) (x : UInt64) (k : Nat) :
    coeffWords
        ((List.range (k / 64)).foldl
          (fun acc j => xorClmulAt acc (idx + j) x (monomial k).words[j]!)
          acc)
        n =
      coeffWords acc n := by
  exact foldl_xorClmulAt_zero_right_coeff
    (List.range (k / 64)) acc idx n x (monomial k).words
    (by
      intro j hj
      exact words_monomial_getElem!_zero_lt (List.mem_range.mp hj))

private theorem foldl_xorClmulAt_monomial_active_low
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_low
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hn := hn) (hbitShift := hbitShift) (hbit := hbit)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

private theorem foldl_xorClmulAt_monomial_active_low_before_shift
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hword : target / 64 = i + k / 64)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        target =
      coeffWords acc target := by
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_low_before_shift
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hword := hword) (hbitShift := hbitShift) (hbit := hbit)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

private theorem foldl_xorClmulAt_monomial_active_high
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hn : n / 64 = i) (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_high
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hidxNext := by simpa [foldl_xorClmulAt_size] using hidxNext)
    (hn := hn) (hbit := hbit)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

private theorem foldl_xorClmulAt_monomial_active_high_after_carry
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hword : target / 64 = i + k / 64 + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        target =
      coeffWords acc target := by
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_monomial_active_high_after_carry
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hidxNext := by simpa [foldl_xorClmulAt_size] using hidxNext)
    (hword := hword) (hbit := hbit)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

private theorem foldl_xorClmulAt_monomial_ne
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hLow : target / 64 ≠ i + k / 64)
    (hHigh : target / 64 ≠ i + k / 64 + 1) :
    coeffWords
        ((List.range (k / 64 + 1)).foldl
          (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
          acc)
        target =
      coeffWords acc target := by
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [coeffWords_xorClmulAt_ne
    (hnLow := hLow) (hnHigh := hHigh)]
  rw [foldl_xorClmulAt_monomial_zero_prefix_coeff]

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
