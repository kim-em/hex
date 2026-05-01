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

private theorem clmul_xor_left_snd_bit (x y z : UInt64) (i : Nat) :
    ((((clmul (x ^^^ y) z).2 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x z).2 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul y z).2 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_xor_left]
  exact UInt64.bit_xor_bne (clmul x z).2 (clmul y z).2 i

private theorem clmul_xor_left_fst_bit (x y z : UInt64) (i : Nat) :
    ((((clmul (x ^^^ y) z).1 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x z).1 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul y z).1 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_xor_left]
  exact UInt64.bit_xor_bne (clmul x z).1 (clmul y z).1 i

private theorem clmul_xor_right_snd_bit (x y z : UInt64) (i : Nat) :
    ((((clmul x (y ^^^ z)).2 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x y).2 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul x z).2 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_comm x (y ^^^ z)]
  rw [clmul_xor_left]
  rw [clmul_comm y x, clmul_comm z x]
  exact UInt64.bit_xor_bne (clmul x y).2 (clmul x z).2 i

private theorem clmul_xor_right_fst_bit (x y z : UInt64) (i : Nat) :
    ((((clmul x (y ^^^ z)).1 >>> i.toUInt64) &&& 1) != 0) =
      (((((clmul x y).1 >>> i.toUInt64) &&& 1) != 0) !=
        ((((clmul x z).1 >>> i.toUInt64) &&& 1) != 0)) := by
  rw [clmul_comm x (y ^^^ z)]
  rw [clmul_xor_left]
  rw [clmul_comm y x, clmul_comm z x]
  exact UInt64.bit_xor_bne (clmul x y).1 (clmul x z).1 i

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

private theorem coeffWords_xorClmulAt_low_xor_left (acc : Array UInt64) {idx n : Nat}
    (x y z : UInt64) (hidx : idx < acc.size) (hn : n / 64 = idx) :
    coeffWords (xorClmulAt acc idx (x ^^^ y) z) n =
      (coeffWords (xorClmulAt acc idx x z) n !=
        ((((clmul y z).2 >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [coeffWords_xorClmulAt_low acc (x ^^^ y) z hidx hn]
  rw [coeffWords_xorClmulAt_low acc x z hidx hn]
  rw [clmul_xor_left_snd_bit]
  cases coeffWords acc n <;>
    cases ((((clmul x z).2 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    cases ((((clmul y z).2 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    rfl

private theorem coeffWords_xorClmulAt_high_xor_left (acc : Array UInt64) {idx n : Nat}
    (x y z : UInt64) (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hn : n / 64 = idx + 1) :
    coeffWords (xorClmulAt acc idx (x ^^^ y) z) n =
      (coeffWords (xorClmulAt acc idx x z) n !=
        ((((clmul y z).1 >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [coeffWords_xorClmulAt_high acc (x ^^^ y) z hidx hidxNext hn]
  rw [coeffWords_xorClmulAt_high acc x z hidx hidxNext hn]
  rw [clmul_xor_left_fst_bit]
  cases coeffWords acc n <;>
    cases ((((clmul x z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    cases ((((clmul y z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
    rfl

private theorem xorWords_getElem! (xs ys : Array UInt64) (i : Nat) :
    (xorWords xs ys)[i]! = xs[i]! ^^^ ys[i]! := by
  simpa only [getElem!_def] using xorWords_get?_getD xs ys i

private theorem normalizeWords_getElem! (words : Array UInt64) (i : Nat) :
    (normalizeWords words)[i]! = words[i]! := by
  simpa only [getElem!_def] using normalizeWords_get?_getD words i

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

private theorem clmul_oneHot_left_low_bit_same_word (x : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hold : old < 64)
    (hbit : old + shift < 64) :
    ((((clmul ((1 : UInt64) <<< shift.toUInt64) x).2 >>>
        (old + shift).toUInt64) &&& 1) != 0) =
      (((x >>> old.toUInt64) &&& 1) != 0) := by
  rw [clmul_oneHot_left_snd x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftLeft,
    UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt hold, Nat.mod_eq_of_lt hbit, bit_eq_one_eq_testBit]
  change (((x.toNat <<< shift) % 18446744073709551616).testBit (old + shift)) =
    x.toNat.testBit old
  rw [show 18446744073709551616 = 2 ^ 64 by rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp [hbit]

private theorem clmul_oneHot_left_low_bit_before_shift_false (x : UInt64) {shift bit : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hbit : bit < shift) :
    ((((clmul ((1 : UInt64) <<< shift.toUInt64) x).2 >>>
        bit.toUInt64) &&& 1) != 0) = false := by
  rw [clmul_oneHot_left_snd x hshift]
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

private theorem clmul_oneHot_left_high_bit_carry_word (x : UInt64) {shift old : Nat}
    (hshiftPos : 0 < shift) (hshift : shift < 64) (hold : old < 64)
    (hbit : 64 ≤ old + shift) :
    ((((clmul ((1 : UInt64) <<< shift.toUInt64) x).1 >>>
        (old + shift - 64).toUInt64) &&& 1) != 0) =
      (((x >>> old.toUInt64) &&& 1) != 0) := by
  have htargetLt : old + shift - 64 < 64 := by omega
  have hshiftCompl : 64 - shift < 64 := by omega
  rw [clmul_oneHot_left_fst x hshift]
  have hshiftNe : shift ≠ 0 := Nat.ne_of_gt hshiftPos
  have hold_eq : 64 - shift + (old + shift - 64) = old := by omega
  simp [hshiftNe, UInt64.bne_zero_eq_toNat_bne_zero, UInt64.toNat_shiftRight,
    UInt64.toNat_and, Nat.mod_eq_of_lt hshiftCompl, Nat.mod_eq_of_lt hold,
    Nat.mod_eq_of_lt htargetLt, bit_eq_one_eq_testBit, Nat.testBit_shiftRight,
    hold_eq]

private theorem clmul_oneHot_left_high_bit_after_carry_false
    (x : UInt64) {shift bit : Nat} (hshift : shift < 64) (hbit : bit < 64)
    (hle : shift ≤ bit) :
    ((((clmul ((1 : UInt64) <<< shift.toUInt64) x).1 >>>
        bit.toUInt64) &&& 1) != 0) = false := by
  rw [clmul_oneHot_left_fst x hshift]
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

private theorem coeffWords_xorClmulAt_oneHot_left_low_same_word
    (acc : Array UInt64) {idx n shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : n / 64 = idx) (hbit : n % 64 + shift < 64) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) (n + shift) =
      (coeffWords acc (n + shift) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hold : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetDiv : (n + shift) / 64 = idx := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  have htargetMod : (n + shift) % 64 = n % 64 + shift := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [coeffWords_xorClmulAt_low acc ((1 : UInt64) <<< shift.toUInt64) x hidx
    htargetDiv]
  rw [htargetMod]
  rw [clmul_oneHot_left_low_bit_same_word x hshiftPos hshift hold hbit]

private theorem coeffWords_xorClmulAt_oneHot_left_low_before_shift
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : target / 64 = idx) (hbit : target % 64 < shift) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) target =
      coeffWords acc target := by
  rw [coeffWords_xorClmulAt_low acc ((1 : UInt64) <<< shift.toUInt64) x hidx hn]
  rw [clmul_oneHot_left_low_bit_before_shift_false x hshiftPos hshift hbit]
  simp

private theorem coeffWords_xorClmulAt_oneHot_left_high_carry_word
    (acc : Array UInt64) {idx n shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hshiftPos : 0 < shift) (hshift : shift < 64)
    (hn : n / 64 = idx) (hbit : 64 ≤ n % 64 + shift) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) (n + shift) =
      (coeffWords acc (n + shift) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have hold : n % 64 < 64 := Nat.mod_lt n (by decide : 0 < 64)
  have htargetDiv : (n + shift) / 64 = idx + 1 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  have htargetMod : (n + shift) % 64 = n % 64 + shift - 64 := by
    have hnSplit := Nat.div_add_mod n 64
    omega
  rw [coeffWords_xorClmulAt_high acc ((1 : UInt64) <<< shift.toUInt64) x hidx
    hidxNext htargetDiv]
  rw [htargetMod]
  rw [clmul_oneHot_left_high_bit_carry_word x hshiftPos hshift hold hbit]

private theorem coeffWords_xorClmulAt_oneHot_left_high_after_carry
    (acc : Array UInt64) {idx target shift : Nat} (x : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size)
    (hshift : shift < 64) (hn : target / 64 = idx + 1)
    (hbit : shift ≤ target % 64) :
    coeffWords (xorClmulAt acc idx ((1 : UInt64) <<< shift.toUInt64) x) target =
      coeffWords acc target := by
  have htargetBit : target % 64 < 64 := Nat.mod_lt target (by decide : 0 < 64)
  rw [coeffWords_xorClmulAt_high acc ((1 : UInt64) <<< shift.toUInt64) x hidx
    hidxNext hn]
  rw [clmul_oneHot_left_high_bit_after_carry_false x hshift htargetBit hbit]
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

private theorem words_monomial_size (k : Nat) :
    (monomial k).words.size = k / 64 + 1 := by
  rw [words_monomial]
  simp

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

private theorem coeffWords_xorClmulAt_monomial_active_zero
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 = 0) :
    coeffWords
        (xorClmulAt acc (i + k / 64) x (monomial k).words[k / 64]!)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have htargetDiv : (n + k) / 64 = i + k / 64 := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  have htargetMod : (n + k) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  rw [words_monomial_getElem!_active k]
  rw [coeffWords_xorClmulAt_low acc x ((1 : UInt64) <<< (k % 64).toUInt64) hidx
    htargetDiv]
  rw [clmul_oneHot_snd x (Nat.mod_lt k (by decide : 0 < 64))]
  simp [hbitShift, htargetMod]

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

private theorem foldl_xorClmulAt_monomial_active_zero
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : i + k / 64 < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 = 0) :
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
  rw [coeffWords_xorClmulAt_monomial_active_zero
    (hidx := by simpa [foldl_xorClmulAt_size] using hidx)
    (hn := hn) (hbitShift := hbitShift)]
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

private theorem clmul_zero_left (x : UInt64) : clmul 0 x = (0, 0) := by
  rw [clmul, pureClmul_zero_left]

private theorem xorClmulAt_zero_left (acc : Array UInt64) (idx : Nat) (x : UInt64) :
    xorClmulAt acc idx 0 x = acc := by
  simp [xorClmulAt, clmul_zero_left, Array.setIfInBounds_getElem!]

private theorem coeffWords_xorClmulAt_zero_left (acc : Array UInt64) (idx n : Nat)
    (x : UInt64) :
    coeffWords (xorClmulAt acc idx 0 x) n = coeffWords acc n := by
  rw [xorClmulAt_zero_left]

private theorem coeffWords_xorClmulAt_xor_left
    (accXY accX accY : Array UInt64) {idx n : Nat} (x y z : UInt64)
    (hsizeX : accX.size = accXY.size) (hsizeY : accY.size = accXY.size)
    (hidx : idx < accXY.size) (hidxNext : idx + 1 < accXY.size)
    (hacc : coeffWords accXY n = (coeffWords accX n != coeffWords accY n)) :
    coeffWords (xorClmulAt accXY idx (x ^^^ y) z) n =
      (coeffWords (xorClmulAt accX idx x z) n !=
        coeffWords (xorClmulAt accY idx y z) n) := by
  by_cases hLow : n / 64 = idx
  · rw [coeffWords_xorClmulAt_low accXY (x ^^^ y) z hidx hLow]
    rw [coeffWords_xorClmulAt_low accX x z (by simpa [hsizeX]) hLow]
    rw [coeffWords_xorClmulAt_low accY y z (by simpa [hsizeY]) hLow]
    rw [clmul_xor_left_snd_bit, hacc]
    cases coeffWords accX n <;>
      cases coeffWords accY n <;>
      cases ((((clmul x z).2 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
      cases ((((clmul y z).2 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
      rfl
  · by_cases hHigh : n / 64 = idx + 1
    · rw [coeffWords_xorClmulAt_high accXY (x ^^^ y) z hidx hidxNext hHigh]
      rw [coeffWords_xorClmulAt_high accX x z (by simpa [hsizeX])
        (by simpa [hsizeX]) hHigh]
      rw [coeffWords_xorClmulAt_high accY y z (by simpa [hsizeY])
        (by simpa [hsizeY]) hHigh]
      rw [clmul_xor_left_fst_bit, hacc]
      cases coeffWords accX n <;>
        cases coeffWords accY n <;>
        cases ((((clmul x z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
        cases ((((clmul y z).1 >>> (n % 64).toUInt64) &&& 1) != 0) <;>
        rfl
    · rw [coeffWords_xorClmulAt_ne accXY (x ^^^ y) z hLow hHigh]
      rw [coeffWords_xorClmulAt_ne accX x z hLow hHigh]
      rw [coeffWords_xorClmulAt_ne accY y z hLow hHigh]
      exact hacc

private theorem foldl_xorClmulAt_xor_left_coeff
    (js : List Nat) (accXY accX accY : Array UInt64) {idx n : Nat}
    (x y : UInt64) (zs : Array UInt64)
    (hsizeX : accX.size = accXY.size) (hsizeY : accY.size = accXY.size)
    (hidx : ∀ j ∈ js, idx + j + 1 < accXY.size)
    (hacc : coeffWords accXY n = (coeffWords accX n != coeffWords accY n)) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) (x ^^^ y) zs[j]!) accXY)
        n =
      (coeffWords
          (js.foldl (fun acc j => xorClmulAt acc (idx + j) x zs[j]!) accX)
          n !=
        coeffWords
          (js.foldl (fun acc j => xorClmulAt acc (idx + j) y zs[j]!) accY)
          n) := by
  induction js generalizing accXY accX accY with
  | nil =>
      simpa using hacc
  | cons j js ih =>
      simp only [List.foldl_cons]
      have hj : idx + j + 1 < accXY.size := hidx j (by simp)
      have htail : ∀ j' ∈ js,
          idx + j' + 1 < (xorClmulAt accXY (idx + j) (x ^^^ y) zs[j]!).size := by
        intro j' hj'
        rw [xorClmulAt_size]
        exact hidx j' (by simp [hj'])
      have hstep :=
        coeffWords_xorClmulAt_xor_left accXY accX accY x y zs[j]!
          (idx := idx + j) (n := n)
          hsizeX hsizeY (by omega) hj hacc
      exact ih
        (accXY := xorClmulAt accXY (idx + j) (x ^^^ y) zs[j]!)
        (accX := xorClmulAt accX (idx + j) x zs[j]!)
        (accY := xorClmulAt accY (idx + j) y zs[j]!)
        (by simp [xorClmulAt_size, hsizeX])
        (by simp [xorClmulAt_size, hsizeY])
        htail hstep

private theorem foldl_mulWords_xor_left_coeff
    (is : List Nat) (accXY accX accY : Array UInt64) {n : Nat}
    (xs ys zs : Array UInt64)
    (hsizeX : accX.size = accXY.size) (hsizeY : accY.size = accXY.size)
    (hidx : ∀ i ∈ is, ∀ j, j < zs.size → i + j + 1 < accXY.size)
    (hacc : coeffWords accXY n = (coeffWords accX n != coeffWords accY n)) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            let y := ys[i]!
            (List.range zs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) (x ^^^ y) zs[j]!)
              acc)
          accXY)
        n =
      (coeffWords
          (is.foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range zs.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x zs[j]!)
                acc)
            accX)
          n !=
        coeffWords
          (is.foldl
            (fun acc i =>
              let y := ys[i]!
              (List.range zs.size).foldl
                (fun acc j => xorClmulAt acc (i + j) y zs[j]!)
                acc)
            accY)
          n) := by
  induction is generalizing accXY accX accY with
  | nil =>
      simpa using hacc
  | cons i is ih =>
      simp only [List.foldl_cons]
      have hinner :=
        foldl_xorClmulAt_xor_left_coeff (List.range zs.size)
          accXY accX accY (idx := i) (n := n) xs[i]! ys[i]! zs
          hsizeX hsizeY
          (by
            intro j hj
            exact hidx i (by simp) j (List.mem_range.mp hj))
          hacc
      have htail : ∀ i' ∈ is, ∀ j, j < zs.size →
          i' + j + 1 <
            ((List.range zs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) (xs[i]! ^^^ ys[i]!) zs[j]!)
              accXY).size := by
        intro i' hi' j hj
        rw [foldl_xorClmulAt_size]
        exact hidx i' (by simp [hi']) j hj
      exact ih
        (accXY :=
          (List.range zs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) (xs[i]! ^^^ ys[i]!) zs[j]!)
            accXY)
        (accX :=
          (List.range zs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! zs[j]!)
            accX)
        (accY :=
          (List.range zs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) ys[i]! zs[j]!)
            accY)
        (by simp [foldl_xorClmulAt_size, hsizeX])
        (by simp [foldl_xorClmulAt_size, hsizeY])
        htail hinner

private theorem coeffWords_xorClmulAt_congr
    (accA accB : Array UInt64) {idx n : Nat} (x y : UInt64)
    (hidxA : idx + 1 < accA.size) (hidxB : idx + 1 < accB.size)
    (hacc : coeffWords accA n = coeffWords accB n) :
    coeffWords (xorClmulAt accA idx x y) n =
      coeffWords (xorClmulAt accB idx x y) n := by
  by_cases hLow : n / 64 = idx
  · rw [coeffWords_xorClmulAt_low accA x y (by omega) hLow]
    rw [coeffWords_xorClmulAt_low accB x y (by omega) hLow]
    rw [hacc]
  · by_cases hHigh : n / 64 = idx + 1
    · rw [coeffWords_xorClmulAt_high accA x y (by omega) hidxA hHigh]
      rw [coeffWords_xorClmulAt_high accB x y (by omega) hidxB hHigh]
      rw [hacc]
    · rw [coeffWords_xorClmulAt_ne accA x y hLow hHigh]
      rw [coeffWords_xorClmulAt_ne accB x y hLow hHigh]
      exact hacc

private theorem foldl_xorClmulAt_congr_coeff
    (js : List Nat) (accA accB : Array UInt64) {idx n : Nat}
    (x : UInt64) (ys : Array UInt64)
    (hidxA : ∀ j ∈ js, idx + j + 1 < accA.size)
    (hidxB : ∀ j ∈ js, idx + j + 1 < accB.size)
    (hacc : coeffWords accA n = coeffWords accB n) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) accA)
        n =
      coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) accB)
        n := by
  induction js generalizing accA accB with
  | nil =>
      simpa using hacc
  | cons j js ih =>
      simp only [List.foldl_cons]
      have hjA : idx + j + 1 < accA.size := hidxA j (by simp)
      have hjB : idx + j + 1 < accB.size := hidxB j (by simp)
      have htailA : ∀ j' ∈ js,
          idx + j' + 1 < (xorClmulAt accA (idx + j) x ys[j]!).size := by
        intro j' hj'
        rw [xorClmulAt_size]
        exact hidxA j' (by simp [hj'])
      have htailB : ∀ j' ∈ js,
          idx + j' + 1 < (xorClmulAt accB (idx + j) x ys[j]!).size := by
        intro j' hj'
        rw [xorClmulAt_size]
        exact hidxB j' (by simp [hj'])
      exact ih
        (accA := xorClmulAt accA (idx + j) x ys[j]!)
        (accB := xorClmulAt accB (idx + j) x ys[j]!)
        htailA htailB
        (coeffWords_xorClmulAt_congr accA accB x ys[j]!
          (idx := idx + j) (n := n) hjA hjB hacc)

private theorem foldl_mulWords_congr_coeff
    (is : List Nat) (accA accB : Array UInt64) {n : Nat}
    (xs ys : Array UInt64)
    (hidxA : ∀ i ∈ is, ∀ j, j < ys.size → i + j + 1 < accA.size)
    (hidxB : ∀ i ∈ is, ∀ j, j < ys.size → i + j + 1 < accB.size)
    (hacc : coeffWords accA n = coeffWords accB n) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          accA)
        n =
      coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          accB)
        n := by
  induction is generalizing accA accB with
  | nil =>
      simpa using hacc
  | cons i is ih =>
      simp only [List.foldl_cons]
      have hinner :=
        foldl_xorClmulAt_congr_coeff (List.range ys.size)
          accA accB (idx := i) (n := n) xs[i]! ys
          (by
            intro j hj
            exact hidxA i (by simp) j (List.mem_range.mp hj))
          (by
            intro j hj
            exact hidxB i (by simp) j (List.mem_range.mp hj))
          hacc
      have htailA : ∀ i' ∈ is, ∀ j, j < ys.size →
          i' + j + 1 <
            ((List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
              accA).size := by
        intro i' hi' j hj
        rw [foldl_xorClmulAt_size]
        exact hidxA i' (by simp [hi']) j hj
      have htailB : ∀ i' ∈ is, ∀ j, j < ys.size →
          i' + j + 1 <
            ((List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
              accB).size := by
        intro i' hi' j hj
        rw [foldl_xorClmulAt_size]
        exact hidxB i' (by simp [hi']) j hj
      exact ih
        (accA :=
          (List.range ys.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
            accA)
        (accB :=
          (List.range ys.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!)
            accB)
        htailA htailB hinner

private theorem foldl_xorClmulAt_zero_left (js : List Nat) (acc : Array UInt64)
    (idx : Nat) (ys : Array UInt64) :
    js.foldl (fun acc j => xorClmulAt acc (idx + j) 0 ys[j]!) acc = acc := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [xorClmulAt_zero_left, ih]

private theorem foldl_xorClmulAt_zero_left_coeff (js : List Nat) (acc : Array UInt64)
    (idx n : Nat) (ys : Array UInt64) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) 0 ys[j]!) acc)
        n =
      coeffWords acc n := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      simp only [List.foldl_cons]
      rw [ih, coeffWords_xorClmulAt_zero_left]

private theorem getElem!_eq_zero_of_size_le (xs : Array UInt64) {i : Nat}
    (hi : xs.size ≤ i) :
    xs[i]! = 0 := by
  rw [getElem!_def]
  rw [Array.getElem?_eq_none]
  · rfl
  · exact hi

private theorem foldl_mulWords_range_add_zero_left_coeff
    (xs ys acc : Array UInt64) (n k : Nat) :
    coeffWords
        ((List.range (xs.size + k)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      coeffWords
        ((List.range xs.size).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show xs.size + Nat.succ k = xs.size + k + 1 by omega]
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [getElem!_eq_zero_of_size_le xs (by omega)]
      rw [foldl_xorClmulAt_zero_left_coeff]
      exact ih

private theorem foldl_mulWords_range_extend_left_coeff
    (xs ys acc : Array UInt64) (n m : Nat) (hsize : xs.size ≤ m) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      coeffWords
        ((List.range xs.size).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n := by
  have hm : m = xs.size + (m - xs.size) := by omega
  rw [hm]
  exact foldl_mulWords_range_add_zero_left_coeff xs ys acc n (m - xs.size)

private theorem foldl_mulWords_left_monomial_zero_prefix_coeff_aux
    (is : List Nat) (acc xs : Array UInt64) (k n : Nat)
    (hmem : ∀ i ∈ is, i < k / 64) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := (monomial k).words[i]!
            (List.range xs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
              acc)
          acc)
        n =
      coeffWords acc n := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < k / 64 := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < k / 64 := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      have hzero : (monomial k).words[i]! = 0 :=
        words_monomial_getElem!_zero_lt (k := k) hi
      rw [hzero]
      rw [ih (acc :=
        (List.range xs.size).foldl (fun acc j => xorClmulAt acc (i + j) 0 xs[j]!) acc)
        htail]
      exact foldl_xorClmulAt_zero_left_coeff (List.range xs.size) acc i n xs

private theorem foldl_mulWords_left_monomial_zero_prefix_coeff
    (acc xs : Array UInt64) (k n : Nat) :
    coeffWords
        ((List.range (k / 64)).foldl
          (fun acc i =>
            let x := (monomial k).words[i]!
            (List.range xs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
              acc)
          acc)
        n =
      coeffWords acc n := by
  exact foldl_mulWords_left_monomial_zero_prefix_coeff_aux
    (List.range (k / 64)) acc xs k n (by
      intro i hi
      exact List.mem_range.mp hi)

private theorem foldl_mulWords_left_monomial_zero_prefix_aux
    (is : List Nat) (acc xs : Array UInt64) (k : Nat)
    (hmem : ∀ i ∈ is, i < k / 64) :
    is.foldl
        (fun acc i =>
          let x := (monomial k).words[i]!
          (List.range xs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
            acc)
        acc =
      acc := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < k / 64 := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < k / 64 := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      have hzero : (monomial k).words[i]! = 0 :=
        words_monomial_getElem!_zero_lt (k := k) hi
      rw [hzero, foldl_xorClmulAt_zero_left, ih (hmem := htail)]

private theorem foldl_mulWords_left_monomial_zero_prefix
    (acc xs : Array UInt64) (k : Nat) :
    (List.range (k / 64)).foldl
        (fun acc i =>
          let x := (monomial k).words[i]!
          (List.range xs.size).foldl
            (fun acc j => xorClmulAt acc (i + j) x xs[j]!)
            acc)
        acc =
      acc := by
  exact foldl_mulWords_left_monomial_zero_prefix_aux
    (List.range (k / 64)) acc xs k (by
      intro i hi
      exact List.mem_range.mp hi)

private theorem coeffWords_xorClmulAt_monomial_left_active_low
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
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
  simpa [hsourceMod, Nat.add_comm] using
    coeffWords_xorClmulAt_oneHot_left_low_same_word
      (acc := acc) (idx := k / 64 + i) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

private theorem coeffWords_xorClmulAt_monomial_left_active_zero
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hn : n / 64 = i)
    (hbitShift : k % 64 = 0) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        (n + k) =
      (coeffWords acc (n + k) !=
        (((x >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  have htargetDiv : (n + k) / 64 = k / 64 + i := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  have htargetMod : (n + k) % 64 = n % 64 := by
    have hnSplit := Nat.div_add_mod n 64
    have hkSplit := Nat.div_add_mod k 64
    omega
  rw [words_monomial_getElem!_active k]
  rw [coeffWords_xorClmulAt_low acc ((1 : UInt64) <<< (k % 64).toUInt64) x hidx
    htargetDiv]
  rw [clmul_oneHot_left_snd x (Nat.mod_lt k (by decide : 0 < 64))]
  simp [hbitShift, htargetMod]

private theorem coeffWords_xorClmulAt_monomial_left_active_low_before_shift
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hword : target / 64 = k / 64 + i)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        target =
      coeffWords acc target := by
  have hshiftPos : 0 < k % 64 := Nat.pos_of_ne_zero hbitShift
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_left_low_before_shift
    (acc := acc) (idx := k / 64 + i) (target := target)
    (shift := k % 64) x hidx hshiftPos hshift hword hbit

private theorem coeffWords_xorClmulAt_monomial_left_active_high
    (acc : Array UInt64) {i k n : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hidxNext : k / 64 + i + 1 < acc.size)
    (hn : n / 64 = i) (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
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
  simpa [hsourceMod, Nat.add_comm] using
    coeffWords_xorClmulAt_oneHot_left_high_carry_word
      (acc := acc) (idx := k / 64 + i) (n := n + k / 64 * 64)
      (shift := k % 64) x hidx hidxNext hshiftPos hshift
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)
      (by
        have hnSplit := Nat.div_add_mod n 64
        omega)

private theorem coeffWords_xorClmulAt_monomial_left_active_high_after_carry
    (acc : Array UInt64) {i k target : Nat} (x : UInt64)
    (hidx : k / 64 + i < acc.size) (hidxNext : k / 64 + i + 1 < acc.size)
    (hword : target / 64 = k / 64 + i + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! x)
        target =
      coeffWords acc target := by
  have hshift : k % 64 < 64 := Nat.mod_lt k (by decide : 0 < 64)
  rw [words_monomial_getElem!_active k]
  exact coeffWords_xorClmulAt_oneHot_left_high_after_carry
    (acc := acc) (idx := k / 64 + i) (target := target)
    (shift := k % 64) x hidx hidxNext hshift hword hbit

private theorem foldl_xorClmulAt_monomial_left_ne
    (acc xs : Array UInt64) {k i target : Nat}
    (hLow : target / 64 ≠ k / 64 + i)
    (hHigh : target / 64 ≠ k / 64 + i + 1) :
    coeffWords
        (xorClmulAt acc (k / 64 + i) (monomial k).words[k / 64]! xs[i]!)
        target =
      coeffWords acc target := by
  exact coeffWords_xorClmulAt_ne
    (acc := acc) (idx := k / 64 + i) (n := target)
    ((monomial k).words[k / 64]!) xs[i]! hLow hHigh

private theorem foldl_xorClmulAt_monomial_left_target_lt
    (js : List Nat) (acc xs : Array UInt64) {k target : Nat}
    (hmem : ∀ j ∈ js, j < xs.size) (hacc : k / 64 + xs.size + 1 ≤ acc.size)
    (htarget : target < k) :
    coeffWords
        (js.foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          acc)
        target =
      coeffWords acc target := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      have hj : j < xs.size := hmem j (by simp)
      have htail : ∀ j' ∈ js, j' < xs.size := by
        intro j' hj'
        exact hmem j' (by simp [hj'])
      simp only [List.foldl_cons]
      rw [ih
        (acc := xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
        htail]
      · by_cases hLow : target / 64 = k / 64 + j
        · have hbitShift : k % 64 ≠ 0 := by
            intro hzero
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            omega
          have hbit : target % 64 < k % 64 := by
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact coeffWords_xorClmulAt_monomial_left_active_low_before_shift
            (acc := acc) (i := j) (k := k) (target := target) (x := xs[j]!)
            (hidx := by omega) hLow hbitShift hbit
        · have hHigh : target / 64 ≠ k / 64 + j + 1 := by
            intro hHigh
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_left_ne
            (acc := acc) (xs := xs) (k := k) (i := j) (target := target)
            hLow hHigh
      · simpa [xorClmulAt_size] using hacc

private theorem foldl_xorClmulAt_monomial_left_source_oob
    (js : List Nat) (acc xs : Array UInt64) {k source : Nat}
    (hmem : ∀ j ∈ js, j < xs.size) (hacc : k / 64 + xs.size + 1 ≤ acc.size)
    (hsource : xs.size ≤ source / 64) :
    coeffWords
        (js.foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          acc)
        (source + k) =
      coeffWords acc (source + k) := by
  induction js generalizing acc with
  | nil =>
      simp
  | cons j js ih =>
      have hj : j < xs.size := hmem j (by simp)
      have htail : ∀ j' ∈ js, j' < xs.size := by
        intro j' hj'
        exact hmem j' (by simp [hj'])
      simp only [List.foldl_cons]
      rw [ih
        (acc := xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
        htail]
      · by_cases hLow : (source + k) / 64 = k / 64 + j
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            exact coeffWords_xorClmulAt_monomial_left_active_low_before_shift
              (acc := acc) (i := j) (k := k) (target := source + k)
              (x := xs[j]!) (hidx := by omega) hLow hbitShift hbit
          · have hsourceWord : source / 64 = j := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = k / 64 + j + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · exact coeffWords_xorClmulAt_monomial_left_active_high_after_carry
                (acc := acc) (i := j) (k := k) (target := source + k)
                (x := xs[j]!) (hidx := by omega) (hidxNext := by omega)
                hHigh hbit
            · have hsourceWord : source / 64 = j := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · exact foldl_xorClmulAt_monomial_left_ne
              (acc := acc) (xs := xs) (k := k) (i := j) (target := source + k)
              hLow hHigh
      · simpa [xorClmulAt_size] using hacc

private theorem foldl_xorClmulAt_monomial_left_prefix_before_source
    (xs : Array UInt64) {k source m : Nat} (hm : m ≤ source / 64)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)))
        (source + k) =
      false := by
  induction m with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [coeffWords]
      have hword :
          ((Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64))[
              (source + k) / 64]?).getD 0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
  | succ m ih =>
      have hm_le : m ≤ source / 64 := by omega
      have hm_lt : m < source / 64 := by omega
      rw [show m + 1 = m.succ by omega]
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [words_monomial_size]
      by_cases hLow : (source + k) / 64 = k / 64 + m
      · by_cases hbit : (source + k) % 64 < k % 64
        · have hbitShift : k % 64 ≠ 0 := by omega
          rw [coeffWords_xorClmulAt_monomial_left_active_low_before_shift
            (acc :=
              (List.range m).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!)
            (hidx := by
              have hsize := foldl_xorClmulAt_size (List.range m)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                (k / 64) (monomial k).words[k / 64]! xs
              have hcap : k / 64 + m <
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                simp
                omega
              simpa [hsize] using hcap)
            hLow hbitShift hbit]
          simpa [words_monomial_size] using ih hm_le
        · have hsourceWord : source / 64 = m := by
            have hsourceSplit := Nat.div_add_mod source 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetSplit := Nat.div_add_mod (source + k) 64
            have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
            omega
          omega
      · by_cases hHigh : (source + k) / 64 = k / 64 + m + 1
        · by_cases hbit : k % 64 ≤ (source + k) % 64
          · rw [coeffWords_xorClmulAt_monomial_left_active_high_after_carry
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m + 1 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              hHigh hbit]
            simpa [words_monomial_size] using ih hm_le
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · rw [foldl_xorClmulAt_monomial_left_ne
            (acc :=
              (List.range m).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (xs := xs) (k := k) (i := m) (target := source + k) hLow hHigh]
          simpa [words_monomial_size] using ih hm_le

private theorem foldl_xorClmulAt_monomial_left_prefix_after_source
    (xs : Array UInt64) {k source m : Nat} (hm : source / 64 + 1 ≤ m)
    (hmSize : m ≤ xs.size) (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc j => xorClmulAt acc (k / 64 + j) (monomial k).words[k / 64]! xs[j]!)
          (Array.replicate ((monomial k).words.size + xs.size) (0 : UInt64)))
        (source + k) =
      coeffWords xs source := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_active : m = source / 64
      · subst hm_active
        rw [show source / 64 + 1 = (source / 64).succ by omega]
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        have hprefix := foldl_xorClmulAt_monomial_left_prefix_before_source xs
          (m := source / 64) (k := k) (source := source) (by omega) hsource
        have hprefix' :
            coeffWords
                ((List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
                (source + k) =
              false := by
          simpa [words_monomial_size] using hprefix
        by_cases hbitShift : k % 64 = 0
        · rw [coeffWords_xorClmulAt_monomial_left_active_zero
            (acc :=
              (List.range (source / 64)).foldl
                (fun acc j => xorClmulAt acc (k / 64 + j)
                  (monomial k).words[k / 64]! xs[j]!)
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
            (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
            (hidx := by
              have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                (k / 64) (monomial k).words[k / 64]! xs
              have hcap : k / 64 + source / 64 <
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                simp
                omega
              simpa [hsize] using hcap) (hn := rfl) hbitShift]
          rw [hprefix']
          have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
            exact (getElem!_def xs (source / 64)).symm
          simp [coeffWords, hget]
        · by_cases hbit : source % 64 + k % 64 < 64
          · rw [coeffWords_xorClmulAt_monomial_left_active_low
              (acc :=
                (List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap) (hn := rfl)
              hbitShift hbit]
            rw [hprefix']
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
          · rw [coeffWords_xorClmulAt_monomial_left_active_high
              (acc :=
                (List.range (source / 64)).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := source / 64) (k := k) (n := source) (x := xs[source / 64]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_xorClmulAt_size (List.range (source / 64))
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + source / 64 + 1 <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hn := rfl) (hbit := by omega)]
            rw [hprefix']
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
      · have hm_tail : source / 64 + 1 ≤ m := by omega
        have hm_gt : source / 64 < m := by omega
        rw [show m + 1 = m.succ by omega]
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = k / 64 + m
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            rw [coeffWords_xorClmulAt_monomial_left_active_low_before_shift
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_xorClmulAt_size (List.range m)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                  (k / 64) (monomial k).words[k / 64]! xs
                have hcap : k / 64 + m <
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              hLow hbitShift hbit]
            simpa [words_monomial_size] using ih hm_tail (by omega)
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = k / 64 + m + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · rw [coeffWords_xorClmulAt_monomial_left_active_high_after_carry
                (acc :=
                  (List.range m).foldl
                    (fun acc j => xorClmulAt acc (k / 64 + j)
                      (monomial k).words[k / 64]! xs[j]!)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
                (i := m) (k := k) (target := source + k) (x := xs[m]!)
                (hidx := by
                  have hsize := foldl_xorClmulAt_size (List.range m)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                    (k / 64) (monomial k).words[k / 64]! xs
                  have hcap : k / 64 + m <
                      (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                (hidxNext := by
                  have hsize := foldl_xorClmulAt_size (List.range m)
                    (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))
                    (k / 64) (monomial k).words[k / 64]! xs
                  have hcap : k / 64 + m + 1 <
                      (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                hHigh hbit]
              simpa [words_monomial_size] using ih hm_tail (by omega)
            · have hsourceWord : source / 64 = m := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · rw [foldl_xorClmulAt_monomial_left_ne
              (acc :=
                (List.range m).foldl
                  (fun acc j => xorClmulAt acc (k / 64 + j)
                    (monomial k).words[k / 64]! xs[j]!)
                  (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)))
              (xs := xs) (k := k) (i := m) (target := source + k) hLow hHigh]
            simpa [words_monomial_size] using ih hm_tail (by omega)

private theorem foldl_mulWords_monomial_active_zero
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size) (hbitShift : k % 64 = 0) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_zero
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hn := rfl) (hbitShift := hbitShift)

private theorem foldl_mulWords_monomial_active_low
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size)
    (hbitShift : k % 64 ≠ 0) (hbit : n % 64 + k % 64 < 64) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_low
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hn := rfl) (hbitShift := hbitShift) (hbit := hbit)

private theorem foldl_mulWords_monomial_active_high
    (acc xs : Array UInt64) {k n : Nat}
    (hidx : n / 64 + k / 64 < acc.size)
    (hidxNext : n / 64 + k / 64 + 1 < acc.size)
    (hbit : 64 ≤ n % 64 + k % 64) :
    coeffWords
        ((List.range (n / 64 + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (n + k) =
      (coeffWords
          ((List.range (n / 64)).foldl
            (fun acc i =>
              let x := xs[i]!
              (List.range (monomial k).words.size).foldl
                (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
                acc)
            acc)
          (n + k) !=
        (((xs[n / 64]! >>> (n % 64).toUInt64) &&& 1) != 0)) := by
  rw [show n / 64 + 1 = (n / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_high
    (acc :=
      (List.range (n / 64)).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[n / 64]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hidxNext := by
      have hsize := foldl_mulWords_size (List.range (n / 64)) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidxNext)
    (hn := rfl) (hbit := hbit)

private theorem foldl_mulWords_monomial_active_low_before_shift
    (acc xs : Array UInt64) {i k target : Nat}
    (hidx : i + k / 64 < acc.size) (hword : target / 64 = i + k / 64)
    (hbitShift : k % 64 ≠ 0) (hbit : target % 64 < k % 64) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_low_before_shift
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hword := hword) (hbitShift := hbitShift) (hbit := hbit)

private theorem foldl_mulWords_monomial_active_high_after_carry
    (acc xs : Array UInt64) {i k target : Nat}
    (hidx : i + k / 64 < acc.size) (hidxNext : i + k / 64 + 1 < acc.size)
    (hword : target / 64 = i + k / 64 + 1) (hbit : k % 64 ≤ target % 64) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_active_high_after_carry
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!)
    (hidx := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidx)
    (hidxNext := by
      have hsize := foldl_mulWords_size (List.range i) acc xs (monomial k).words
      rw [words_monomial_size] at hsize
      simpa [hsize] using hidxNext)
    (hword := hword) (hbit := hbit)

private theorem foldl_mulWords_monomial_ne
    (acc xs : Array UInt64) {i k target : Nat}
    (hLow : target / 64 ≠ i + k / 64)
    (hHigh : target / 64 ≠ i + k / 64 + 1) :
    coeffWords
        ((List.range (i + 1)).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords
        ((List.range i).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target := by
  rw [show i + 1 = i.succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [words_monomial_size]
  exact foldl_xorClmulAt_monomial_ne
    (acc :=
      (List.range i).foldl
        (fun acc i =>
          let x := xs[i]!
          (List.range (k / 64 + 1)).foldl
            (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
            acc)
        acc)
    (x := xs[i]!) (hLow := hLow) (hHigh := hHigh)

private theorem foldl_mulWords_monomial_target_lt
    (is : List Nat) (acc xs : Array UInt64) {k target : Nat}
    (hmem : ∀ i ∈ is, i < xs.size)
    (hacc : xs.size + (k / 64 + 1) ≤ acc.size) (htarget : target < k) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        target =
      coeffWords acc target := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < xs.size := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < xs.size := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      rw [ih
        (acc :=
          (List.range (monomial k).words.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
            acc)
        htail]
      · rw [words_monomial_size]
        by_cases hLow : target / 64 = i + k / 64
        · have hbitShift : k % 64 ≠ 0 := by
            intro hzero
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            omega
          have hbit : target % 64 < k % 64 := by
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_active_low_before_shift
            (acc := acc) (i := i) (k := k) (target := target) (x := xs[i]!)
            (hidx := by omega) hLow hbitShift hbit
        · have hHigh : target / 64 ≠ i + k / 64 + 1 := by
            intro hHigh
            have htargetSplit := Nat.div_add_mod target 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetBit := Nat.mod_lt target (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            omega
          exact foldl_xorClmulAt_monomial_ne
            (acc := acc) (i := i) (k := k) (target := target) (x := xs[i]!)
            hLow hHigh
      · simpa [foldl_xorClmulAt_size] using hacc

private theorem foldl_mulWords_monomial_source_oob
    (is : List Nat) (acc xs : Array UInt64) {k source : Nat}
    (hmem : ∀ i ∈ is, i < xs.size)
    (hacc : xs.size + (k / 64 + 1) ≤ acc.size)
    (hsource : xs.size ≤ source / 64) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          acc)
        (source + k) =
      coeffWords acc (source + k) := by
  induction is generalizing acc with
  | nil =>
      simp
  | cons i is ih =>
      have hi : i < xs.size := hmem i (by simp)
      have htail : ∀ i' ∈ is, i' < xs.size := by
        intro i' hi'
        exact hmem i' (by simp [hi'])
      simp only [List.foldl_cons]
      rw [ih
        (acc :=
          (List.range (monomial k).words.size).foldl
            (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
            acc)
        htail]
      · rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = i + k / 64
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            exact foldl_xorClmulAt_monomial_active_low_before_shift
              (acc := acc) (i := i) (k := k) (target := source + k) (x := xs[i]!)
              (hidx := by omega) hLow hbitShift hbit
          · have hsourceWord : source / 64 = i := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = i + k / 64 + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · exact foldl_xorClmulAt_monomial_active_high_after_carry
                (acc := acc) (i := i) (k := k) (target := source + k)
                (x := xs[i]!) (hidx := by omega) (hidxNext := by omega)
                hHigh hbit
            · have hsourceWord : source / 64 = i := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · exact foldl_xorClmulAt_monomial_ne
              (acc := acc) (i := i) (k := k) (target := source + k) (x := xs[i]!)
              hLow hHigh
      · simpa [foldl_xorClmulAt_size] using hacc

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

private theorem coeffWords_replicate_zero (size n : Nat) :
    coeffWords (Array.replicate size (0 : UInt64)) n = false := by
  rw [coeffWords]
  by_cases h : n / 64 < (Array.replicate size (0 : UInt64)).size
  · rw [Array.getElem?_eq_getElem h]
    simp
  · rw [Array.getElem?_eq_none]
    · simp
    · exact Nat.le_of_not_gt h

private theorem coeffWords_empty (n : Nat) :
    coeffWords #[] n = false := by
  rw [coeffWords]
  simp

private theorem coeffWords_mulWords_common_left
    (xs zs : Array UInt64) (n m : Nat) (hm : xs.size ≤ m) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range zs.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x zs[j]!)
              acc)
          (Array.replicate (m + zs.size) (0 : UInt64)))
        n =
      coeffWords (mulWords xs zs) n := by
  unfold mulWords
  by_cases hzs : zs.isEmpty
  · have hcommon :=
      foldl_mulWords_range_extend_left_coeff xs zs
        (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
    rw [hcommon]
    have hzsize : zs.size = 0 := by
      simpa [Array.isEmpty] using hzs
    simp only [hzs, hzsize, List.range_zero, List.foldl_nil, Bool.or_true, ↓reduceIte]
    rw [foldl_keep, coeffWords_replicate_zero, coeffWords_empty]
  · by_cases hxs : xs.isEmpty
    · have hcommon :=
        foldl_mulWords_range_extend_left_coeff xs zs
          (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
      rw [hcommon]
      have hxsize : xs.size = 0 := by
        simpa [Array.isEmpty] using hxs
      simp [hxs, hzs, hxsize, coeffWords_replicate_zero, coeffWords_empty]
    · have hcommon :=
        foldl_mulWords_range_extend_left_coeff xs zs
          (Array.replicate (m + zs.size) (0 : UInt64)) n m hm
      rw [hcommon]
      have hcongr :=
        foldl_mulWords_congr_coeff (List.range xs.size)
          (Array.replicate (m + zs.size) (0 : UInt64))
          (Array.replicate (xs.size + zs.size) (0 : UInt64))
          (n := n) xs zs
          (by
            intro i hi j hj
            have hi' : i < xs.size := List.mem_range.mp hi
            simpa using (by omega : i + j + 1 < m + zs.size))
          (by
            intro i hi j hj
            have hi' : i < xs.size := List.mem_range.mp hi
            simpa using (by omega : i + j + 1 < xs.size + zs.size))
          (by
            rw [coeffWords_replicate_zero, coeffWords_replicate_zero])
      rw [hcongr]
      simp [hxs, hzs]

private theorem coeffWords_mulWords_xor_left_same_size
    (xs ys zs : Array UInt64) (n : Nat) (hsize : xs.size = ys.size) :
    coeffWords (mulWords (xorWords xs ys) zs) n =
      (coeffWords (mulWords xs zs) n != coeffWords (mulWords ys zs) n) := by
  unfold mulWords
  by_cases hzs : zs.isEmpty
  · simp [hzs]
    exact coeffWords_empty n
  · by_cases hxs : xs.isEmpty
    · have hxempty : xs = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        simpa [Array.isEmpty] using hxs
      have hyempty : ys = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        have hxsize : xs.size = 0 := by
          simp [hxempty]
        omega
      simp [hxempty, hyempty, xorWords, coeffWords_empty]
    · have hys : ys.isEmpty = false := by
        have hxsize : xs.size ≠ 0 := by
          intro hz
          apply hxs
          simpa [Array.isEmpty] using hz
        have hysize : ys.size ≠ 0 := by omega
        rw [Array.isEmpty]
        simp [hysize]
      have hxor : (xorWords xs ys).isEmpty = false := by
        rw [Array.isEmpty]
        have hxsize : xs.size ≠ 0 := by
          intro hz
          apply hxs
          simpa [Array.isEmpty] using hz
        have hmax : max xs.size ys.size ≠ 0 := by omega
        simp [xorWords_size, hmax]
      have hzarr : zs ≠ #[] := by
        intro hz
        apply hzs
        simp [hz]
      simp [hxs, hys, hxor, xorWords_size, hsize, xorWords_getElem!, hzarr]
      exact foldl_mulWords_xor_left_coeff (List.range ys.size)
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (Array.replicate (ys.size + zs.size) (0 : UInt64))
        (n := n) xs ys zs rfl rfl
        (by
          intro i hi j hj
          have hi' : i < ys.size := List.mem_range.mp hi
          simp
          omega)
        (by
          rw [coeffWords_replicate_zero]
          rfl)

private theorem coeffWords_mulWords_xor_left
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (xorWords xs ys) zs) n =
      (coeffWords (mulWords xs zs) n != coeffWords (mulWords ys zs) n) := by
  let m := max xs.size ys.size
  rw [← coeffWords_mulWords_common_left (xorWords xs ys) zs n m (by simp [m])]
  rw [← coeffWords_mulWords_common_left xs zs n m
    (by simpa [m] using Nat.le_max_left xs.size ys.size)]
  rw [← coeffWords_mulWords_common_left ys zs n m
    (by simpa [m] using Nat.le_max_right xs.size ys.size)]
  simp only [xorWords_getElem!]
  exact foldl_mulWords_xor_left_coeff (List.range m)
    (Array.replicate (m + zs.size) (0 : UInt64))
    (Array.replicate (m + zs.size) (0 : UInt64))
    (Array.replicate (m + zs.size) (0 : UInt64))
    (n := n) xs ys zs rfl rfl
    (by
      intro i hi j hj
      have hi' : i < m := List.mem_range.mp hi
      simpa using (by omega : i + j + 1 < m + zs.size))
    (by
      rw [coeffWords_replicate_zero]
      rfl)

private theorem coeffWords_mulWords_monomial_lt
    (xs : Array UInt64) {k target : Nat} (htarget : target < k) :
    coeffWords (mulWords xs (monomial k).words) target = false := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · simp [hxs, coeffWords]
  · have hys : ¬ (monomial k).words.isEmpty := by
      rw [words_monomial]
      simp
    simp [hxs, hys]
    rw [foldl_mulWords_monomial_target_lt]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[target / 64]?).getD
              0 = 0 := by
        by_cases h : target / 64 < (Array.replicate (xs.size + (monomial k).words.size)
            (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword]
      rw [UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro i hi
      exact List.mem_range.mp hi
    · simp [words_monomial_size]
    · exact htarget

private theorem coeffWords_mulWords_monomial_source_oob
    (xs : Array UInt64) {k source : Nat} (hsource : xs.size ≤ source / 64) :
    coeffWords (mulWords xs (monomial k).words) (source + k) = false := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · simp [hxs, coeffWords]
  · have hys : ¬ (monomial k).words.isEmpty := by
      rw [words_monomial]
      simp
    simp [hxs, hys]
    rw [foldl_mulWords_monomial_source_oob]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[(source + k) / 64]?).getD
              0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword]
      rw [UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro i hi
      exact List.mem_range.mp hi
    · simp [words_monomial_size]
    · exact hsource

private theorem foldl_mulWords_monomial_prefix_before_source
    (xs : Array UInt64) {k source m : Nat} (hm : m ≤ source / 64)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)))
        (source + k) =
      false := by
  induction m with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [coeffWords]
      have hword :
          ((Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))[
              (source + k) / 64]?).getD 0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
  | succ m ih =>
      have hm_le : m ≤ source / 64 := by omega
      have hm_lt : m < source / 64 := by omega
      rw [show m + 1 = m.succ by omega]
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [words_monomial_size]
      by_cases hLow : (source + k) / 64 = m + k / 64
      · by_cases hbit : (source + k) % 64 < k % 64
        · have hbitShift : k % 64 ≠ 0 := by omega
          rw [foldl_xorClmulAt_monomial_active_low_before_shift
            (acc :=
              (List.range m).foldl
                (fun acc i =>
                  let x := xs[i]!
                  (List.range (k / 64 + 1)).foldl
                    (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                    acc)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!)
            (hidx := by
              have hsize := foldl_mulWords_size (List.range m)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                xs (monomial k).words
              rw [words_monomial_size] at hsize
              have hcap : m + k / 64 <
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                simp
                omega
              simpa [hsize] using hcap)
            hLow hbitShift hbit]
          simpa [words_monomial_size] using ih hm_le
        · have hsourceWord : source / 64 = m := by
            have hsourceSplit := Nat.div_add_mod source 64
            have hkSplit := Nat.div_add_mod k 64
            have htargetSplit := Nat.div_add_mod (source + k) 64
            have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
            have hkBit := Nat.mod_lt k (by decide : 0 < 64)
            have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
            omega
          omega
      · by_cases hHigh : (source + k) / 64 = m + k / 64 + 1
        · by_cases hbit : k % 64 ≤ (source + k) % 64
          · rw [foldl_xorClmulAt_monomial_active_high_after_carry
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              (hidxNext := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 + 1 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
              hHigh hbit]
            simpa [words_monomial_size] using ih hm_le
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · rw [foldl_xorClmulAt_monomial_ne
            (acc :=
              (List.range m).foldl
                (fun acc i =>
                  let x := xs[i]!
                  (List.range (k / 64 + 1)).foldl
                    (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                    acc)
                (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
            (i := m) (k := k) (target := source + k) (x := xs[m]!) hLow hHigh]
          simpa [words_monomial_size] using ih hm_le

private theorem foldl_mulWords_monomial_prefix_after_source
    (xs : Array UInt64) {k source m : Nat} (hm : source / 64 + 1 ≤ m)
    (hmSize : m ≤ xs.size)
    (hsource : source / 64 < xs.size) :
    coeffWords
        ((List.range m).foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range (monomial k).words.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x (monomial k).words[j]!)
              acc)
          (Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64)))
        (source + k) =
      coeffWords xs source := by
  induction m with
  | zero =>
      omega
  | succ m ih =>
      by_cases hm_active : m = source / 64
      · subst hm_active
        by_cases hbitShift : k % 64 = 0
        · rw [foldl_mulWords_monomial_active_zero
            (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
            (xs := xs) (k := k) (n := source)
            (hidx := by simp [words_monomial_size]; omega) hbitShift]
          have hprefix := foldl_mulWords_monomial_prefix_before_source xs
            (m := source / 64) (k := k) (source := source) (by omega) hsource
          rw [hprefix]
          have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
            exact (getElem!_def xs (source / 64)).symm
          simp [coeffWords, hget]
        · by_cases hbit : source % 64 + k % 64 < 64
          · rw [foldl_mulWords_monomial_active_low
              (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
              (xs := xs) (k := k) (n := source)
              (hidx := by simp [words_monomial_size]; omega) hbitShift hbit]
            have hprefix := foldl_mulWords_monomial_prefix_before_source xs
              (m := source / 64) (k := k) (source := source) (by omega) hsource
            rw [hprefix]
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
          · rw [foldl_mulWords_monomial_active_high
              (acc := Array.replicate (xs.size + (monomial k).words.size) (0 : UInt64))
              (xs := xs) (k := k) (n := source)
              (hidx := by simp [words_monomial_size]; omega)
              (hidxNext := by simp [words_monomial_size]; omega)
              (hbit := by omega)]
            have hprefix := foldl_mulWords_monomial_prefix_before_source xs
              (m := source / 64) (k := k) (source := source) (by omega) hsource
            rw [hprefix]
            have hget : (xs[source / 64]?).getD 0 = xs[source / 64]! := by
              exact (getElem!_def xs (source / 64)).symm
            simp [coeffWords, hget]
      · have hm_tail : source / 64 + 1 ≤ m := by omega
        have hm_gt : source / 64 < m := by omega
        rw [show m + 1 = m.succ by omega]
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [words_monomial_size]
        by_cases hLow : (source + k) / 64 = m + k / 64
        · by_cases hbit : (source + k) % 64 < k % 64
          · have hbitShift : k % 64 ≠ 0 := by omega
            rw [foldl_xorClmulAt_monomial_active_low_before_shift
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!)
              (hidx := by
                have hsize := foldl_mulWords_size (List.range m)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                  xs (monomial k).words
                rw [words_monomial_size] at hsize
                have hcap : m + k / 64 <
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                  simp
                  omega
                simpa [hsize] using hcap)
            hLow hbitShift hbit]
            simpa [words_monomial_size] using ih hm_tail (by omega)
          · have hsourceWord : source / 64 = m := by
              have hsourceSplit := Nat.div_add_mod source 64
              have hkSplit := Nat.div_add_mod k 64
              have htargetSplit := Nat.div_add_mod (source + k) 64
              have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
              have hkBit := Nat.mod_lt k (by decide : 0 < 64)
              have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
              omega
            omega
        · by_cases hHigh : (source + k) / 64 = m + k / 64 + 1
          · by_cases hbit : k % 64 ≤ (source + k) % 64
            · rw [foldl_xorClmulAt_monomial_active_high_after_carry
                (acc :=
                  (List.range m).foldl
                    (fun acc i =>
                      let x := xs[i]!
                      (List.range (k / 64 + 1)).foldl
                        (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                        acc)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
                (i := m) (k := k) (target := source + k) (x := xs[m]!)
                (hidx := by
                  have hsize := foldl_mulWords_size (List.range m)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                    xs (monomial k).words
                  rw [words_monomial_size] at hsize
                  have hcap : m + k / 64 <
                      (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                (hidxNext := by
                  have hsize := foldl_mulWords_size (List.range m)
                    (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64))
                    xs (monomial k).words
                  rw [words_monomial_size] at hsize
                  have hcap : m + k / 64 + 1 <
                      (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)).size := by
                    simp
                    omega
                  simpa [hsize] using hcap)
                hHigh hbit]
              simpa [words_monomial_size] using ih hm_tail (by omega)
            · have hsourceWord : source / 64 = m := by
                have hsourceSplit := Nat.div_add_mod source 64
                have hkSplit := Nat.div_add_mod k 64
                have htargetSplit := Nat.div_add_mod (source + k) 64
                have hsourceBit := Nat.mod_lt source (by decide : 0 < 64)
                have hkBit := Nat.mod_lt k (by decide : 0 < 64)
                have htargetBit := Nat.mod_lt (source + k) (by decide : 0 < 64)
                omega
              omega
          · rw [foldl_xorClmulAt_monomial_ne
              (acc :=
                (List.range m).foldl
                  (fun acc i =>
                    let x := xs[i]!
                    (List.range (k / 64 + 1)).foldl
                      (fun acc j => xorClmulAt acc (i + j) xs[i]! (monomial k).words[j]!)
                      acc)
                  (Array.replicate (xs.size + (k / 64 + 1)) (0 : UInt64)))
              (i := m) (k := k) (target := source + k) (x := xs[m]!) hLow hHigh]
            simpa [words_monomial_size] using ih hm_tail (by omega)

private theorem coeffWords_mulWords_monomial_source
    (xs : Array UInt64) {k source : Nat} (hsource : source / 64 < xs.size) :
    coeffWords (mulWords xs (monomial k).words) (source + k) =
      coeffWords xs source := by
  unfold mulWords
  have hxs : ¬xs.isEmpty := by
    intro hempty
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hempty
    omega
  have hys : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  simp [hxs, hys]
  exact foldl_mulWords_monomial_prefix_after_source xs
    (m := xs.size) (k := k) (source := source) (by omega) (by omega) hsource

private theorem coeffWords_monomial_mulWords_lt
    (xs : Array UInt64) {k target : Nat} (htarget : target < k) :
    coeffWords (mulWords (monomial k).words xs) target = false := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  by_cases hxs : xs.isEmpty
  · simp [hmon, hxs, coeffWords]
  · simp [hmon, hxs]
    rw [words_monomial_size]
    rw [show k / 64 + 1 = (k / 64).succ by omega]
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_mulWords_left_monomial_zero_prefix]
    rw [foldl_xorClmulAt_monomial_left_target_lt]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))[target / 64]?).getD
              0 = 0 := by
        by_cases h : target / 64 <
            (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro j hj
      exact List.mem_range.mp hj
    · simp
      omega
    · exact htarget

private theorem coeffWords_monomial_mulWords_source_oob
    (xs : Array UInt64) {k source : Nat} (hsource : xs.size ≤ source / 64) :
    coeffWords (mulWords (monomial k).words xs) (source + k) = false := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  by_cases hxs : xs.isEmpty
  · simp [hmon, hxs, coeffWords]
  · simp [hmon, hxs]
    rw [words_monomial_size]
    rw [show k / 64 + 1 = (k / 64).succ by omega]
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_mulWords_left_monomial_zero_prefix]
    rw [foldl_xorClmulAt_monomial_left_source_oob]
    · rw [coeffWords]
      have hword :
          ((Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64))[(source + k) / 64]?).getD
              0 = 0 := by
        by_cases h : (source + k) / 64 <
            (Array.replicate (k / 64 + 1 + xs.size) (0 : UInt64)).size
        · rw [Array.getElem?_eq_getElem h]
          simp
        · rw [Array.getElem?_eq_none]
          · rfl
          · exact Nat.le_of_not_gt h
      rw [hword, UInt64.bne_zero_eq_toNat_bne_zero]
      simp
    · intro j hj
      exact List.mem_range.mp hj
    · simp
      omega
    · exact hsource

private theorem coeffWords_monomial_mulWords_source
    (xs : Array UInt64) {k source : Nat} (hsource : source / 64 < xs.size) :
    coeffWords (mulWords (monomial k).words xs) (source + k) =
      coeffWords xs source := by
  unfold mulWords
  have hmon : ¬ (monomial k).words.isEmpty := by
    rw [words_monomial]
    simp
  have hxs : ¬ xs.isEmpty := by
    intro hempty
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hempty
    omega
  simp [hmon, hxs]
  rw [words_monomial_size]
  rw [show k / 64 + 1 = (k / 64).succ by omega]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [foldl_mulWords_left_monomial_zero_prefix]
  simpa [words_monomial_size] using
    foldl_xorClmulAt_monomial_left_prefix_after_source xs
      (m := xs.size) (k := k) (source := source) (by omega) (by omega) hsource

private def clmulCoeffAt (idx : Nat) (x y : UInt64) (n : Nat) : Bool :=
  if n / 64 = idx then
    (((clmul x y).2 >>> (n % 64).toUInt64) &&& 1) != 0
  else if n / 64 = idx + 1 then
    (((clmul x y).1 >>> (n % 64).toUInt64) &&& 1) != 0
  else
    false

private def xorBoolList (bits : List Bool) : Bool :=
  bits.foldl (fun acc bit => acc != bit) false

private theorem Bool.bne_assoc (a b c : Bool) :
    ((a != b) != c) = (a != (b != c)) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem foldl_bne_start (bits : List Bool) (acc : Bool) :
    bits.foldl (fun acc bit => acc != bit) acc =
      (acc != xorBoolList bits) := by
  unfold xorBoolList
  induction bits generalizing acc with
  | nil =>
      cases acc <;> rfl
  | cons bit bits ih =>
      simp only [List.foldl_cons]
      rw [ih (acc != bit), ih (false != bit)]
      generalize htail : List.foldl (fun acc bit => acc != bit) false bits = tail
      cases acc <;> cases bit <;> cases tail <;> rfl

private theorem xorBoolList_cons (bit : Bool) (bits : List Bool) :
    xorBoolList (bit :: bits) = (bit != xorBoolList bits) := by
  unfold xorBoolList
  simp only [List.foldl_cons]
  rw [foldl_bne_start]
  cases bit <;> rfl

private theorem xorBoolList_append (xs ys : List Bool) :
    xorBoolList (xs ++ ys) = (xorBoolList xs != xorBoolList ys) := by
  unfold xorBoolList
  rw [List.foldl_append, foldl_bne_start]
  simp [xorBoolList]

private theorem Bool.bne_medial (a b c d : Bool) :
    ((a != b) != (c != d)) = ((a != c) != (b != d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem List.flatMap_const_nil {α β : Type} (xs : List α) :
    xs.flatMap (fun _ => ([] : List β)) = [] := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [ih]

private theorem List.flatMap_empty_input {α β : Type} (f : α → List β) :
    ([] : List α).flatMap f = [] := by
  rfl

private theorem List.flatMap_singleton {α β : Type} (xs : List α) (f : α → β) :
    xs.flatMap (fun x => [f x]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [ih]

private theorem List.flatMap_congr_left {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [h x (by simp)]
      rw [ih]
      intro y hy
      exact h y (by simp [hy])

private theorem xorBoolList_flatMap_append {α : Type}
    (xs : List α) (left right : α → List Bool) :
    xorBoolList (xs.flatMap fun x => left x ++ right x) =
      (xorBoolList (xs.flatMap left) != xorBoolList (xs.flatMap right)) := by
  induction xs with
  | nil =>
      simp [xorBoolList]
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, xorBoolList_append, xorBoolList_append, ih]
      rw [xorBoolList_append]
      generalize xorBoolList (left x) = a
      generalize xorBoolList (List.flatMap left xs) = b
      generalize xorBoolList (right x) = c
      generalize xorBoolList (List.flatMap right xs) = d
      cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem xorBoolList_wordPairs_swap
    (m n : Nat) (term : Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i => (List.range n).map (fun j => term i j))
          (List.range m)) =
      xorBoolList
        (List.flatMap
          (fun j => (List.range m).map (fun i => term i j))
          (List.range n)) := by
  induction m with
  | zero =>
      simp [xorBoolList, List.flatMap_const_nil]
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, ih]
      rw [List.flatMap_empty_input]
      simp only [List.append_nil]
      have hcols :
          xorBoolList
              (List.flatMap
                (fun j => (List.range m ++ [m]).map (fun i => term i j))
                (List.range n)) =
            (xorBoolList
                (List.flatMap
                  (fun j => (List.range m).map (fun i => term i j))
                  (List.range n)) !=
              xorBoolList ((List.range n).map (fun j => term m j))) := by
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [xorBoolList_flatMap_append]
        rw [List.flatMap_singleton]
      rw [hcols]

private theorem xorBoolList_flatMap_congr_xor {α : Type}
    {xs : List α} {left right : α → List Bool}
    (h : ∀ x, x ∈ xs → xorBoolList (left x) = xorBoolList (right x)) :
    xorBoolList (xs.flatMap left) = xorBoolList (xs.flatMap right) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [xorBoolList_append, xorBoolList_append]
      rw [h x (by simp), ih]
      intro y hy
      exact h y (by simp [hy])

private theorem xorBoolList_map_xorBoolList {α : Type}
    (xs : List α) (terms : α → List Bool) :
    xorBoolList (xs.map (fun x => xorBoolList (terms x))) =
      xorBoolList (xs.flatMap terms) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [xorBoolList_cons, xorBoolList_append, ih]

/-- Reindex a triple XOR from the left-associated word-pair grouping
`(i,j),k` to the right-associated grouping `i,(j,k)`, keeping the outer
source word `i` fixed and swapping the two inner finite ranges. -/
private theorem xorBoolList_wordTriples_assoc
    (m n o : Nat) (term : Nat → Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j => (List.range o).map (fun k => term i j k))
              (List.range n))
          (List.range m)) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun k => (List.range n).map (fun j => term i j k))
              (List.range o))
          (List.range m)) := by
  apply xorBoolList_flatMap_congr_xor
  intro i _hi
  exact xorBoolList_wordPairs_swap n o (fun j k => term i j k)

/-- Array-specialized triple reindexing theorem for raw multiplication
associativity proof terms.  Later coefficient bridges instantiate `term` with
the source-word contribution predicate built from `xs[i]!`, `ys[j]!`, and
`zs[k]!`. -/
private theorem xorBoolList_sourceTriples_assoc
    (xs ys zs : Array UInt64) (term : Nat → Nat → Nat → Bool) :
    xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j => (List.range zs.size).map (fun k => term i j k))
              (List.range ys.size))
          (List.range xs.size)) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun k => (List.range ys.size).map (fun j => term i j k))
              (List.range zs.size))
          (List.range xs.size)) := by
  exact xorBoolList_wordTriples_assoc xs.size ys.size zs.size term

/-- XOR a list of machine words as the word-level analogue of `xorBoolList`. -/
private def xorWordList : List UInt64 → UInt64
  | [] => 0
  | word :: words => word ^^^ xorWordList words

/-- The raw word contribution of a single `clmul x y` placed at word offset
`idx`, projected to result word slot `slot`. -/
private def clmulWordAt (idx : Nat) (x y : UInt64) (slot : Nat) : UInt64 :=
  if slot = idx then
    (clmul x y).2
  else if slot = idx + 1 then
    (clmul x y).1
  else
    0

private theorem UInt64.xor_assoc (a b c : UInt64) :
    (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_xor, Nat.xor_assoc]

private theorem UInt64.xor_zero (a : UInt64) :
    a ^^^ 0 = a := by
  apply UInt64.toNat_inj.mp
  simp

private theorem UInt64.zero_xor (a : UInt64) :
    0 ^^^ a = a := by
  apply UInt64.toNat_inj.mp
  simp

private theorem Array.getElem!_setIfInBounds_ne {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (v : α) (hne : i ≠ j) :
    (xs.setIfInBounds i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hne]
  · simp [hi]

private theorem replicate_zero_getElem! (size slot : Nat) :
    (Array.replicate size (0 : UInt64))[slot]! = 0 := by
  rw [Array.getElem!_eq_getD]
  by_cases hslot : slot < (Array.replicate size (0 : UInt64)).size
  · have hslot' : slot < size := by
      simpa using hslot
    simp [Array.getD, hslot']
  · have hslot' : size ≤ slot := by
      simpa using Nat.le_of_not_gt hslot
    simp [Array.getD, hslot']
    rfl

private theorem xorWordList_append (xs ys : List UInt64) :
    xorWordList (xs ++ ys) = xorWordList xs ^^^ xorWordList ys := by
  induction xs with
  | nil =>
      simp [xorWordList]
  | cons x xs ih =>
      simp only [List.cons_append, xorWordList]
      rw [ih, UInt64.xor_assoc]

private theorem xorClmulAt_getElem!_contrib
    (acc : Array UInt64) {idx slot : Nat} (x y : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size) :
    (xorClmulAt acc idx x y)[slot]! =
      acc[slot]! ^^^ clmulWordAt idx x y slot := by
  unfold xorClmulAt clmulWordAt
  by_cases hLow : slot = idx
  · subst slot
    simp [hidx]
  · by_cases hHigh : slot = idx + 1
    · subst slot
      simp [hidx, hidxNext]
    · have hLow' : idx ≠ slot := Ne.symm hLow
      have hHigh' : idx + 1 ≠ slot := Ne.symm hHigh
      rcases hprod : clmul x y with ⟨hi, lo⟩
      simp [hidx, hidxNext, hLow, hHigh,
        Array.getElem!_setIfInBounds_ne, hLow', hHigh']

private theorem foldl_xorClmulAt_getElem!_contrib
    (js : List Nat) (acc : Array UInt64) (idx : Nat) (x : UInt64)
    (ys : Array UInt64) (slot : Nat)
    (hbound : ∀ j ∈ js, idx + j + 1 < acc.size) :
    (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc)[slot]! =
      (acc[slot]! ^^^
        xorWordList (js.map (fun j => clmulWordAt (idx + j) x ys[j]! slot))) := by
  induction js generalizing acc with
  | nil =>
      simp [xorWordList]
  | cons j js ih =>
      simp only [List.foldl_cons, List.map_cons]
      have htail := ih (xorClmulAt acc (idx + j) x ys[j]!)
        (by
          intro j' hj'
          have h := hbound j' (by simp [hj'])
          simpa [xorClmulAt_size] using h)
      rw [htail]
      have hhead := xorClmulAt_getElem!_contrib acc (idx := idx + j)
        (slot := slot) x ys[j]!
        (by
          have h := hbound j (by simp)
          omega)
        (hbound j (by simp))
      rw [hhead, xorWordList, UInt64.xor_assoc]

private theorem foldl_mulWords_getElem!_contrib
    (is : List Nat) (acc : Array UInt64) (xs ys : Array UInt64) (slot : Nat)
    (hbound : ∀ i ∈ is, ∀ j ∈ List.range ys.size, i + j + 1 < acc.size) :
    (is.foldl
      (fun acc i =>
        let x := xs[i]!
        (List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
          acc)
      acc)[slot]! =
      (acc[slot]! ^^^
        xorWordList
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
            is)) := by
  induction is generalizing acc with
  | nil =>
      simp [xorWordList]
  | cons i is ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      have htail := ih
        ((List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) xs[i]! ys[j]!) acc)
        (by
          intro i' hi' j hj
          have h := hbound i' (by simp [hi']) j hj
          simpa [foldl_xorClmulAt_size] using h)
      rw [htail]
      have hinner := foldl_xorClmulAt_getElem!_contrib
        (List.range ys.size) acc i xs[i]! ys slot
        (by
          intro j hj
          exact hbound i (by simp) j hj)
      rw [hinner]
      rw [xorWordList_append, UInt64.xor_assoc]

private theorem clmulCoeffAt_zero_left (idx : Nat) (y : UInt64) (n : Nat) :
    clmulCoeffAt idx 0 y n = false := by
  unfold clmulCoeffAt
  rw [clmul_zero_left]
  by_cases hLow : n / 64 = idx
  · simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1 <;> simp [hLow, hHigh]

private theorem clmulCoeffAt_xor_left
    (idx : Nat) (x y z : UInt64) (n : Nat) :
    clmulCoeffAt idx (x ^^^ y) z n =
      (clmulCoeffAt idx x z n != clmulCoeffAt idx y z n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · simp [hLow]
    rw [clmul_xor_left_snd_bit]
  · by_cases hHigh : n / 64 = idx + 1
    · simp [hHigh]
      rw [clmul_xor_left_fst_bit]
    · simp [hLow, hHigh]

private theorem clmulCoeffAt_zero_right (idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x 0 n = false := by
  unfold clmulCoeffAt
  rw [clmul_zero_right]
  by_cases hLow : n / 64 = idx
  · simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1 <;> simp [hLow, hHigh]

private theorem clmulCoeffAt_xor_right
    (idx : Nat) (x y z : UInt64) (n : Nat) :
    clmulCoeffAt idx x (y ^^^ z) n =
      (clmulCoeffAt idx x y n != clmulCoeffAt idx x z n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · simp [hLow]
    rw [clmul_xor_right_snd_bit]
  · by_cases hHigh : n / 64 = idx + 1
    · simp [hHigh]
      rw [clmul_xor_right_fst_bit]
    · simp [hLow, hHigh]

private theorem clmulCoeffAt_xorWordList_left
    (words : List UInt64) (idx : Nat) (z : UInt64) (n : Nat) :
    clmulCoeffAt idx (xorWordList words) z n =
      xorBoolList (words.map (fun word => clmulCoeffAt idx word z n)) := by
  induction words with
  | nil =>
      change clmulCoeffAt idx 0 z n = false
      exact clmulCoeffAt_zero_left idx z n
  | cons word words ih =>
      rw [xorWordList, clmulCoeffAt_xor_left]
      change (clmulCoeffAt idx word z n != clmulCoeffAt idx (xorWordList words) z n) =
        xorBoolList (clmulCoeffAt idx word z n ::
          words.map (fun word => clmulCoeffAt idx word z n))
      rw [xorBoolList_cons, ih]

private theorem clmulCoeffAt_xorWordList_right
    (words : List UInt64) (idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x (xorWordList words) n =
      xorBoolList (words.map (fun word => clmulCoeffAt idx x word n)) := by
  induction words with
  | nil =>
      change clmulCoeffAt idx x 0 n = false
      exact clmulCoeffAt_zero_right idx x n
  | cons word words ih =>
      rw [xorWordList, clmulCoeffAt_xor_right]
      change (clmulCoeffAt idx x word n != clmulCoeffAt idx x (xorWordList words) n) =
        xorBoolList (clmulCoeffAt idx x word n ::
          words.map (fun word => clmulCoeffAt idx x word n))
      rw [xorBoolList_cons, ih]

private theorem coeffWords_xorClmulAt_contrib
    (acc : Array UInt64) {idx n : Nat} (x y : UInt64)
    (hidx : idx < acc.size) (hidxNext : idx + 1 < acc.size) :
    coeffWords (xorClmulAt acc idx x y) n =
      (coeffWords acc n != clmulCoeffAt idx x y n) := by
  unfold clmulCoeffAt
  by_cases hLow : n / 64 = idx
  · rw [coeffWords_xorClmulAt_low acc x y hidx hLow]
    simp [hLow]
  · by_cases hHigh : n / 64 = idx + 1
    · rw [coeffWords_xorClmulAt_high acc x y hidx hidxNext hHigh]
      simp [hHigh]
    · rw [coeffWords_xorClmulAt_ne acc x y hLow hHigh]
      simp [hLow, hHigh]

private theorem foldl_xorClmulAt_coeff_contrib
    (js : List Nat) (acc : Array UInt64) (idx : Nat) (x : UInt64)
    (ys : Array UInt64) (n : Nat)
    (hbound : ∀ j ∈ js, idx + j + 1 < acc.size) :
    coeffWords
        (js.foldl (fun acc j => xorClmulAt acc (idx + j) x ys[j]!) acc)
        n =
      (coeffWords acc n !=
        xorBoolList (js.map (fun j => clmulCoeffAt (idx + j) x ys[j]! n))) := by
  induction js generalizing acc with
  | nil =>
      simp [xorBoolList]
  | cons j js ih =>
      simp only [List.foldl_cons, List.map_cons]
      have hidx : idx + j < acc.size := by
        have h := hbound j (by simp)
        omega
      have hidxNext : idx + j + 1 < acc.size := hbound j (by simp)
      rw [ih]
      · rw [coeffWords_xorClmulAt_contrib acc x ys[j]! hidx hidxNext]
        rw [xorBoolList_cons, Bool.bne_assoc]
      · intro j' hj'
        have h := hbound j' (by simp [hj'])
        simpa [xorClmulAt_size] using h

private theorem foldl_mulWords_coeff_contrib
    (is : List Nat) (acc : Array UInt64) (xs ys : Array UInt64) (n : Nat)
    (hbound : ∀ i ∈ is, ∀ j ∈ List.range ys.size, i + j + 1 < acc.size) :
    coeffWords
        (is.foldl
          (fun acc i =>
            let x := xs[i]!
            (List.range ys.size).foldl
              (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
              acc)
          acc)
        n =
      (coeffWords acc n !=
        xorBoolList
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulCoeffAt (i + j) xs[i]! ys[j]! n))
            is)) := by
  induction is generalizing acc with
  | nil =>
      simp [xorBoolList]
  | cons i is ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      · have hinner := foldl_xorClmulAt_coeff_contrib
          (List.range ys.size) acc i xs[i]! ys n
          (by
            intro j hj
            exact hbound i (by simp) j hj)
        rw [hinner]
        rw [xorBoolList_append, Bool.bne_assoc]
      · intro i' hi' j hj
        have h := hbound i' (by simp [hi']) j hj
        simpa [foldl_xorClmulAt_size] using h

private theorem coeffWords_mulWords_contrib (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs ys) n =
      xorBoolList
        (List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulCoeffAt (i + j) xs[i]! ys[j]! n))
          (List.range xs.size)) := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · have hxsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hxs
    simp [hxs, hxsize, coeffWords_empty, xorBoolList]
  · by_cases hys : ys.isEmpty
    · have hysize : ys.size = 0 := by
        simpa [Array.isEmpty] using hys
      have hflat :
          List.flatMap (fun _ : Nat => ([] : List Bool)) (List.range xs.size) = [] := by
        generalize hlist : List.range xs.size = is
        induction is with
        | nil => rfl
        | cons i is ih =>
            simp [List.flatMap_cons]
      simp [hxs, hys, hysize, coeffWords_empty, xorBoolList, hflat]
    · simp [hxs, hys]
      rw [foldl_mulWords_coeff_contrib]
      · rw [coeffWords_replicate_zero]
        simp
      · intro i hi j hj
        have hi' : i < xs.size := List.mem_range.mp hi
        have hj' : j < ys.size := List.mem_range.mp hj
        simp
        omega

/-- A raw product word is the XOR of all source word-pair contributions whose
low or high `clmul` word lands in that result slot. -/
private theorem mulWords_getElem!_contrib
    (xs ys : Array UInt64) (slot : Nat) :
    (mulWords xs ys)[slot]! =
      xorWordList
        (List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
          (List.range xs.size)) := by
  unfold mulWords
  by_cases hxs : xs.isEmpty
  · have hxsize : xs.size = 0 := by
      simpa [Array.isEmpty] using hxs
    simp [hxs, hxsize, xorWordList]
    rfl
  · by_cases hys : ys.isEmpty
    · have hysize : ys.size = 0 := by
        simpa [Array.isEmpty] using hys
      have hflat :
          List.flatMap (fun _ : Nat => ([] : List UInt64)) (List.range xs.size) = [] := by
        generalize hlist : List.range xs.size = is
        induction is with
        | nil => rfl
        | cons i is ih =>
            simp [List.flatMap_cons]
      simp [hxs, hys, hysize, xorWordList, hflat]
      rfl
    · simp [hxs, hys]
      rw [foldl_mulWords_getElem!_contrib]
      · rw [replicate_zero_getElem!, UInt64.zero_xor]
      · intro i hi j hj
        have hi' : i < xs.size := List.mem_range.mp hi
        have hj' : j < ys.size := List.mem_range.mp hj
        simp
        omega

/-- Expand a later `clmul` coefficient whose left input is an intermediate raw
product word into source word-pair contributions. -/
private theorem clmulCoeffAt_mulWords_left_contrib
    (xs ys : Array UInt64) (slot idx : Nat) (z : UInt64) (n : Nat) :
    clmulCoeffAt idx (mulWords xs ys)[slot]! z n =
      xorBoolList
        ((List.flatMap
          (fun i =>
            (List.range ys.size).map
              (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
          (List.range xs.size)).map
          (fun word => clmulCoeffAt idx word z n)) := by
  rw [mulWords_getElem!_contrib, clmulCoeffAt_xorWordList_left]

/-- Expand a later `clmul` coefficient whose right input is an intermediate raw
product word into source word-pair contributions. -/
private theorem clmulCoeffAt_mulWords_right_contrib
    (ys zs : Array UInt64) (slot idx : Nat) (x : UInt64) (n : Nat) :
    clmulCoeffAt idx x (mulWords ys zs)[slot]! n =
      xorBoolList
        ((List.flatMap
          (fun j =>
            (List.range zs.size).map
              (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
          (List.range ys.size)).map
          (fun word => clmulCoeffAt idx x word n)) := by
  rw [mulWords_getElem!_contrib, clmulCoeffAt_xorWordList_right]

/-- Source-word contribution list for one coefficient of the left-associated
raw product `(xs * ys) * zs`.  The outer product contributes a word slot and a
`zs` source word; each such intermediate word is expanded back to the
`xs`/`ys` source pair contributions that created it. -/
private def leftAssocSourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) : List Bool :=
  List.flatMap
    (fun slot =>
      List.flatMap
        (fun k =>
          (List.flatMap
            (fun i =>
              (List.range ys.size).map
                (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
            (List.range xs.size)).map
            (fun word => clmulCoeffAt (slot + k) word zs[k]! n))
        (List.range zs.size))
    (List.range (mulWords xs ys).size)

/-- Source-word contribution list for one coefficient of the right-associated
raw product `xs * (ys * zs)`.  The outer product contributes an `xs` source
word and an intermediate word slot; each intermediate word is expanded back to
the `ys`/`zs` source pair contributions that created it. -/
private def rightAssocSourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) : List Bool :=
  List.flatMap
    (fun i =>
      List.flatMap
        (fun slot =>
          (List.flatMap
            (fun j =>
              (List.range zs.size).map
                (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
            (List.range ys.size)).map
            (fun word => clmulCoeffAt (i + slot) xs[i]! word n))
        (List.range (mulWords ys zs).size))
    (List.range xs.size)

/-- Contributions from one fixed source triple `(i,j,k)` to the left-associated
word product, varying only the intermediate `(xs * ys)` result slot. -/
private def leftAssocFixedTripleContribs
    (i j k : Nat) (x y z : UInt64) (n slotBound : Nat) : List Bool :=
  (List.range slotBound).map
    (fun slot => clmulCoeffAt (slot + k) (clmulWordAt (i + j) x y slot) z n)

/-- Contributions from one fixed source triple `(i,j,k)` to the right-associated
word product, varying only the intermediate `(ys * zs)` result slot. -/
private def rightAssocFixedTripleContribs
    (i j k : Nat) (x y z : UInt64) (n slotBound : Nat) : List Bool :=
  (List.range slotBound).map
    (fun slot => clmulCoeffAt (i + slot) x (clmulWordAt (j + k) y z slot) n)

/-- The raw product has enough intermediate slots to contain every source
word-pair contribution selected by the source ranges. -/
private theorem mulWords_size_source_pair
    {xs ys : Array UInt64} {i j : Nat}
    (hi : i ∈ List.range xs.size) (hj : j ∈ List.range ys.size) :
    i + j + 1 < (mulWords xs ys).size := by
  have hiLt : i < xs.size := List.mem_range.mp hi
  have hjLt : j < ys.size := List.mem_range.mp hj
  have hxs : ¬ xs.isEmpty := by
    intro h
    have hsize : xs.size = 0 := by
      simpa [Array.isEmpty] using h
    omega
  have hys : ¬ ys.isEmpty := by
    intro h
    have hsize : ys.size = 0 := by
      simpa [Array.isEmpty] using h
    omega
  unfold mulWords
  simp [hxs, hys, foldl_mulWords_size]
  omega

/-- Fixed source-word associativity for carry-less multiplication after
expanding only the intermediate packed-word slot. -/
private theorem xorBoolList_assoc_fixed_sourceTriple
    (i j k : Nat) (x y z : UInt64) (n leftBound rightBound : Nat)
    (hleft : i + j + 1 < leftBound) (hright : j + k + 1 < rightBound) :
    xorBoolList (leftAssocFixedTripleContribs i j k x y z n leftBound) =
      xorBoolList (rightAssocFixedTripleContribs i j k x y z n rightBound) := by
  sorry

/-- Regroup the left-associated source expansion by fixed source triples rather
than by intermediate product slot first. -/
private theorem leftAssocSourceTripleContribs_by_fixed
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (leftAssocSourceTripleContribs xs ys zs n) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j =>
                List.flatMap
                  (fun k =>
                    leftAssocFixedTripleContribs i j k xs[i]! ys[j]! zs[k]! n
                      (mulWords xs ys).size)
                  (List.range zs.size))
              (List.range ys.size))
          (List.range xs.size)) := by
  sorry

/-- Regroup the right-associated source expansion by fixed source triples rather
than by intermediate product slot first. -/
private theorem rightAssocSourceTripleContribs_by_fixed
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (rightAssocSourceTripleContribs xs ys zs n) =
      xorBoolList
        (List.flatMap
          (fun i =>
            List.flatMap
              (fun j =>
                List.flatMap
                  (fun k =>
                    rightAssocFixedTripleContribs i j k xs[i]! ys[j]! zs[k]! n
                      (mulWords ys zs).size)
                  (List.range zs.size))
              (List.range ys.size))
          (List.range xs.size)) := by
  sorry

private theorem leftAssocSourceTripleContribs_slot
    (xs ys zs : Array UInt64) (slot n : Nat) :
    xorBoolList
        ((List.range zs.size).map
          (fun k => clmulCoeffAt (slot + k) (mulWords xs ys)[slot]! zs[k]! n)) =
      xorBoolList
        (List.flatMap
          (fun k =>
            (List.flatMap
              (fun i =>
                (List.range ys.size).map
                  (fun j => clmulWordAt (i + j) xs[i]! ys[j]! slot))
              (List.range xs.size)).map
              (fun word => clmulCoeffAt (slot + k) word zs[k]! n))
          (List.range zs.size)) := by
  rw [← xorBoolList_map_xorBoolList]
  congr 1
  apply List.map_congr_left
  intro k _hk
  exact clmulCoeffAt_mulWords_left_contrib xs ys slot (slot + k) zs[k]! n

private theorem rightAssocSourceTripleContribs_slot
    (xs ys zs : Array UInt64) (i n : Nat) :
    xorBoolList
        ((List.range (mulWords ys zs).size).map
          (fun slot => clmulCoeffAt (i + slot) xs[i]! (mulWords ys zs)[slot]! n)) =
      xorBoolList
        (List.flatMap
          (fun slot =>
            (List.flatMap
              (fun j =>
                (List.range zs.size).map
                  (fun k => clmulWordAt (j + k) ys[j]! zs[k]! slot))
              (List.range ys.size)).map
              (fun word => clmulCoeffAt (i + slot) xs[i]! word n))
          (List.range (mulWords ys zs).size)) := by
  rw [← xorBoolList_map_xorBoolList]
  congr 1
  apply List.map_congr_left
  intro slot _hslot
  exact clmulCoeffAt_mulWords_right_contrib ys zs slot (i + slot) xs[i]! n

/-- Coefficients of the left-associated raw product expand to the finite XOR
of the source-word triples contributing to `(xs * ys) * zs`. -/
private theorem coeffWords_mulWords_left_assoc_sourceTriples
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (mulWords xs ys) zs) n =
      xorBoolList (leftAssocSourceTripleContribs xs ys zs n) := by
  rw [coeffWords_mulWords_contrib]
  unfold leftAssocSourceTripleContribs
  exact xorBoolList_flatMap_congr_xor
    (fun slot _hslot => leftAssocSourceTripleContribs_slot xs ys zs slot n)

/-- Coefficients of the right-associated raw product expand to the finite XOR
of the source-word triples contributing to `xs * (ys * zs)`. -/
private theorem coeffWords_mulWords_right_assoc_sourceTriples
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (mulWords ys zs)) n =
      xorBoolList (rightAssocSourceTripleContribs xs ys zs n) := by
  rw [coeffWords_mulWords_contrib]
  unfold rightAssocSourceTripleContribs
  exact xorBoolList_flatMap_congr_xor
    (fun i _hi => rightAssocSourceTripleContribs_slot xs ys zs i n)

/-- The source-triple XOR expansions of the two raw associated products
contribute the same coefficient.  Proving this requires the fixed source-word
triple bridge: summing over the intermediate word slot in `(xs[i] * ys[j]) *
zs[k]` matches summing over the intermediate word slot in `xs[i] * (ys[j] *
zs[k])`. -/
private theorem xorBoolList_assoc_sourceTripleContribs
    (xs ys zs : Array UInt64) (n : Nat) :
    xorBoolList (leftAssocSourceTripleContribs xs ys zs n) =
      xorBoolList (rightAssocSourceTripleContribs xs ys zs n) := by
  rw [leftAssocSourceTripleContribs_by_fixed, rightAssocSourceTripleContribs_by_fixed]
  apply xorBoolList_flatMap_congr_xor
  intro i hi
  apply xorBoolList_flatMap_congr_xor
  intro j hj
  apply xorBoolList_flatMap_congr_xor
  intro k hk
  exact xorBoolList_assoc_fixed_sourceTriple i j k xs[i]! ys[j]! zs[k]! n
    (mulWords xs ys).size (mulWords ys zs).size
    (mulWords_size_source_pair hi hj)
    (mulWords_size_source_pair hj hk)

private theorem clmulCoeffAt_comm (i j : Nat) (x y : UInt64) (n : Nat) :
    clmulCoeffAt (i + j) x y n = clmulCoeffAt (j + i) y x n := by
  unfold clmulCoeffAt
  rw [Nat.add_comm i j, clmul_comm x y]

/-- Coefficients of the raw packed product are symmetric in the two input word
arrays. This is the local bridge from word-level `clmul_comm` to polynomial
multiplication commutativity. -/
private theorem coeffWords_mulWords_comm (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs ys) n = coeffWords (mulWords ys xs) n := by
  rw [coeffWords_mulWords_contrib xs ys n, coeffWords_mulWords_contrib ys xs n]
  rw [xorBoolList_wordPairs_swap xs.size ys.size
    (fun i j => clmulCoeffAt (i + j) xs[i]! ys[j]! n)]
  congr 1
  apply List.flatMap_congr_left
  intro j hj
  apply List.map_congr_left
  intro i hi
  exact clmulCoeffAt_comm i j xs[i]! ys[j]! n

private theorem coeffWords_mulWords_normalize_left
    (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords (normalizeWords xs) ys) n =
      coeffWords (mulWords xs ys) n := by
  rw [← coeffWords_mulWords_common_left (normalizeWords xs) ys n xs.size
    (normalizeWords_size_le xs)]
  rw [← coeffWords_mulWords_common_left xs ys n xs.size (Nat.le_refl xs.size)]
  simp [normalizeWords_getElem!]

private theorem coeffWords_mulWords_normalize_right
    (xs ys : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (normalizeWords ys)) n =
      coeffWords (mulWords xs ys) n := by
  rw [coeffWords_mulWords_comm xs (normalizeWords ys)]
  rw [coeffWords_mulWords_normalize_left ys xs]
  rw [coeffWords_mulWords_comm ys xs]

private theorem coeffWords_mulWords_ofWords_left
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (ofWords (mulWords xs ys)).words zs) n =
      coeffWords (mulWords (mulWords xs ys) zs) n := by
  change coeffWords (mulWords (normalizeWords (mulWords xs ys)) zs) n =
    coeffWords (mulWords (mulWords xs ys) zs) n
  exact coeffWords_mulWords_normalize_left (mulWords xs ys) zs n

private theorem coeffWords_mulWords_ofWords_right
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords xs (ofWords (mulWords ys zs)).words) n =
      coeffWords (mulWords xs (mulWords ys zs)) n := by
  change coeffWords (mulWords xs (normalizeWords (mulWords ys zs))) n =
    coeffWords (mulWords xs (mulWords ys zs)) n
  exact coeffWords_mulWords_normalize_right xs (mulWords ys zs) n

/-- Raw packed multiplication is coefficientwise associative.  This is the
source-triple frontier: the two source-triple expansions above reduce raw
associativity to a fixed-triple word contribution identity. -/
private theorem coeffWords_mulWords_assoc
    (xs ys zs : Array UInt64) (n : Nat) :
    coeffWords (mulWords (mulWords xs ys) zs) n =
      coeffWords (mulWords xs (mulWords ys zs)) n := by
  rw [coeffWords_mulWords_left_assoc_sourceTriples,
    coeffWords_mulWords_right_assoc_sourceTriples]
  exact xorBoolList_assoc_sourceTripleContribs xs ys zs n

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

/-- Left distributivity of packed `GF(2)` polynomial multiplication over
addition. -/
theorem left_distrib (p r q : GF2Poly) :
    (p + r) * q = p * q + r * q := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_add_eq_bne, coeff_mul, coeff_mul]
  change
    coeffWords (mulWords (normalizeWords (xorWords p.words r.words)) q.words) n =
      (coeffWords (mulWords p.words q.words) n !=
        coeffWords (mulWords r.words q.words) n)
  let raw := xorWords p.words r.words
  let m := raw.size
  have hraw := coeffWords_mulWords_xor_left p.words r.words q.words n
  rw [← coeffWords_mulWords_common_left raw q.words n m (by simp [m])] at hraw
  rw [← coeffWords_mulWords_common_left (normalizeWords raw) q.words n m
    (by
      dsimp [m, raw]
      exact normalizeWords_size_le _)]
  simpa [raw, normalizeWords_getElem!] using hraw

/-- Packed `GF(2)` polynomial multiplication is commutative. -/
theorem mul_comm (p q : GF2Poly) :
    p * q = q * p := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  exact coeffWords_mulWords_comm p.words q.words n

/-- Right distributivity of packed `GF(2)` polynomial multiplication over
addition. -/
theorem right_distrib (p q r : GF2Poly) :
    p * (q + r) = p * q + p * r := by
  rw [mul_comm p (q + r), left_distrib, mul_comm q p, mul_comm r p]

/-- Packed `GF(2)` polynomial multiplication is associative. -/
theorem mul_assoc (p q r : GF2Poly) :
    (p * q) * r = p * (q * r) := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mul]
  change
    coeffWords (mulWords (ofWords (mulWords p.words q.words)).words r.words) n =
      coeffWords (mulWords p.words (ofWords (mulWords q.words r.words)).words) n
  rw [coeffWords_mulWords_ofWords_left, coeffWords_mulWords_ofWords_right]
  exact coeffWords_mulWords_assoc p.words q.words r.words n

private theorem coeff_shiftLeft_lt (p : GF2Poly) {k n : Nat} (hn : n < k) :
    (p.shiftLeft k).coeff n = false := by
  rw [coeff_shiftLeft]
  by_cases hbitShift : k % 64 = 0
  · simp [hbitShift]
    have hword : n / 64 < k / 64 := by
      have hnSplit := Nat.div_add_mod n 64
      have hkSplit := Nat.div_add_mod k 64
      have hnBit := Nat.mod_lt n (by decide : 0 < 64)
      omega
    rw [coeffWords]
    have hget :
        (((Array.replicate (k / 64) (0 : UInt64)) ++ p.words)[n / 64]?).getD 0 = 0 := by
      rw [Array.getElem?_append_left]
      · simp [hword]
      · simp [hword]
    rw [hget, UInt64.bne_zero_eq_toNat_bne_zero]
    simp
  · simp [hbitShift, coeffWords_replicate_append_shiftLeftBitsList_lt p.words hbitShift hn]

private theorem coeff_shiftLeft_add_source_oob
    (p : GF2Poly) {k source : Nat} (hsource : p.words.size ≤ source / 64) :
    (p.shiftLeft k).coeff (source + k) = false := by
  rw [coeff_shiftLeft]
  by_cases hbitShift : k % 64 = 0
  · have hcoeff : p.coeff source = false := by
      simp [coeff, coeffWords, hsource]
    simp [hbitShift, coeffWords_replicate_append_add_of_mod_eq_zero, coeff] at hcoeff ⊢
    exact hcoeff
  · simp [hbitShift,
      coeffWords_replicate_append_shiftLeftBitsList_add_of_not_word
        p.words hbitShift (Nat.not_lt.mpr hsource)]

/-- Right multiplication by the monomial `x^k` shifts packed GF(2)
polynomials left by `k` coefficients. -/
theorem mul_monomial (q : GF2Poly) (k : Nat) :
    q * monomial k = q.mulXk k := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mulXk]
  by_cases hn : n < k
  · rw [coeffWords_mulWords_monomial_lt q.words hn]
    exact (coeff_shiftLeft_lt q hn).symm
  · let source := n - k
    have hn_eq : n = source + k := by
      dsimp [source]
      omega
    rw [hn_eq]
    by_cases hsource : source / 64 < q.words.size
    · rw [coeffWords_mulWords_monomial_source q.words hsource]
      exact (coeff_shiftLeft_add_of_word_lt (p := q) (k := k) (n := source) hsource).symm
    · have hsource_le : q.words.size ≤ source / 64 := Nat.le_of_not_gt hsource
      rw [coeffWords_mulWords_monomial_source_oob q.words hsource_le]
      exact (coeff_shiftLeft_add_source_oob q hsource_le).symm

/-- Left multiplication by the monomial `x^k` shifts packed GF(2)
polynomials left by `k` coefficients. -/
theorem monomial_mul (k : Nat) (q : GF2Poly) :
    monomial k * q = q.mulXk k := by
  apply ext_coeff
  intro n
  rw [coeff_mul, coeff_mulXk]
  by_cases hn : n < k
  · rw [coeffWords_monomial_mulWords_lt q.words hn]
    exact (coeff_shiftLeft_lt q hn).symm
  · let source := n - k
    have hn_eq : n = source + k := by
      dsimp [source]
      omega
    rw [hn_eq]
    by_cases hsource : source / 64 < q.words.size
    · rw [coeffWords_monomial_mulWords_source q.words hsource]
      exact (coeff_shiftLeft_add_of_word_lt (p := q) (k := k) (n := source) hsource).symm
    · have hsource_le : q.words.size ≤ source / 64 := Nat.le_of_not_gt hsource
      rw [coeffWords_monomial_mulWords_source_oob q.words hsource_le]
      exact (coeff_shiftLeft_add_source_oob q hsource_le).symm

/-- Expanding a quotient update by an added monomial gives the product update
used by long division. -/
theorem add_monomial_mul (quot q : GF2Poly) (k : Nat) :
    (quot + monomial k) * q = quot * q + q.mulXk k := by
  rw [left_distrib, monomial_mul]

end GF2Poly
end Hex
