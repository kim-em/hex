import HexGF2.Basic

/-!
Carry-less `UInt64` multiplication for `hex-gf2`.

`pureClmul` is the logical reference implementation used in proofs and by the
fallback runtime path. The `@[extern]` boundary lets compiled code swap in a C
shim that may dispatch to architecture intrinsics, but the trusted contract is
still exactly the `(hi, lo)` product returned by `pureClmul`.
-/
namespace Hex

/-- XOR the carry-less partial product `a * x^bitIdx` into the `(hi, lo)`
accumulator. The caller must supply `bitIdx < 64`. -/
private def clmulAccumulateBit (acc : UInt64 × UInt64) (a : UInt64) (bitIdx : Nat) :
    UInt64 × UInt64 :=
  let (hi, lo) := acc
  if bitIdx = 0 then
    (hi, lo ^^^ a)
  else
    let loPart := a <<< bitIdx.toUInt64
    let hiPart := a >>> (64 - bitIdx).toUInt64
    (hi ^^^ hiPart, lo ^^^ loPart)

/-- Pure Lean carry-less multiplication of two 64-bit words, returned as
`(hi, lo)` for the 128-bit product. -/
def pureClmul (a b : UInt64) : UInt64 × UInt64 :=
  (List.range 64).foldl
    (fun acc bitIdx =>
      if ((b >>> bitIdx.toUInt64) &&& 1) != 0 then
        clmulAccumulateBit acc a bitIdx
      else
        acc)
    (0, 0)

private theorem oneHotWord_bit {hot bit : Nat} (hhot : hot < 64) (hbit : bit < 64) :
    (((((1 : UInt64) <<< hot.toUInt64) >>> bit.toUInt64) &&& 1) != 0) = (hot == bit) := by
  by_cases h : hot = bit
  · subst h
    simp [GF2Poly.oneHotWord_bit_self hbit]
  · rw [GF2Poly.oneHotWord_bit_ne hhot hbit h]
    simp [h]

private theorem clmulAccumulateBit_zero (a : UInt64) (bit : Nat) :
    clmulAccumulateBit (0, 0) a bit =
      if bit = 0 then (0, a) else (a >>> (64 - bit).toUInt64, a <<< bit.toUInt64) := by
  by_cases h : bit = 0 <;> simp [clmulAccumulateBit, h]

private theorem oneHot_shiftLeft_of_sum_lt {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hsum : hot + bitIdx < 64) :
    (((1 : UInt64) <<< hot.toUInt64) <<< bitIdx.toUInt64) =
      ((1 : UInt64) <<< (hot + bitIdx).toUInt64) := by
  apply UInt64.toNat_inj.mp
  have hpowHot : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  have hpowSum : 2 ^ (hot + bitIdx) < 2 ^ 64 :=
    Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hsum
  simp [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hhot,
    Nat.mod_eq_of_lt hbitIdx, Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt hpowHot,
    Nat.mod_eq_of_lt hpowSum, Nat.shiftLeft_eq]
  rw [← Nat.pow_add]
  exact Nat.mod_eq_of_lt hpowSum

private theorem oneHot_shiftLeft_of_sum_ge {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hsum : 64 ≤ hot + bitIdx) :
    (((1 : UInt64) <<< hot.toUInt64) <<< bitIdx.toUInt64) = 0 := by
  apply UInt64.toNat_inj.mp
  have hpowHot : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  simp [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hhot,
    Nat.mod_eq_of_lt hbitIdx, Nat.mod_eq_of_lt hpowHot, Nat.shiftLeft_eq]
  have hdiv : 2 ^ 64 ∣ 2 ^ hot * 2 ^ bitIdx := by
    rw [← Nat.pow_add]
    exact Nat.pow_dvd_pow 2 hsum
  exact Nat.mod_eq_zero_of_dvd hdiv

private theorem oneHot_shiftRight_of_sum_lt {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hbitIdxPos : 0 < bitIdx)
    (hsum : hot + bitIdx < 64) :
    (((1 : UInt64) <<< hot.toUInt64) >>> (64 - bitIdx).toUInt64) = 0 := by
  apply UInt64.toNat_inj.mp
  have hpowHot : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  have hshift : 64 - bitIdx < 64 := by omega
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt hhot, Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hpowHot,
    Nat.shiftLeft_eq]
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt
    (Nat.pow_lt_pow_of_lt (by decide : 1 < 2) (by omega))

private theorem oneHot_shiftRight_of_sum_ge {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hsum : 64 ≤ hot + bitIdx) :
    (((1 : UInt64) <<< hot.toUInt64) >>> (64 - bitIdx).toUInt64) =
      ((1 : UInt64) <<< (hot + bitIdx - 64).toUInt64) := by
  apply UInt64.toNat_inj.mp
  have hpowHot : 2 ^ hot < 2 ^ 64 := Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hhot
  have hshift : 64 - bitIdx < 64 := by omega
  have htarget : hot + bitIdx - 64 < 64 := by omega
  have hpowTarget : 2 ^ (hot + bitIdx - 64) < 2 ^ 64 :=
    Nat.pow_lt_pow_of_lt (by decide : 1 < 2) htarget
  have hexp : hot = (64 - bitIdx) + (hot + bitIdx - 64) := by omega
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt hhot, Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt htarget,
    Nat.mod_eq_of_lt hpowHot, Nat.mod_eq_of_lt hpowTarget, Nat.shiftLeft_eq]
  rw [hexp, Nat.pow_add]
  rw [Nat.shiftRight_eq_div_pow]
  have hrhs : 64 - bitIdx + (hot + bitIdx - 64) + bitIdx - 64 =
      hot + bitIdx - 64 := by
    omega
  rw [hrhs]
  have hpos : 0 < 2 ^ (64 - bitIdx) := Nat.pow_pos (by decide : 0 < 2)
  exact Nat.mul_div_right _ hpos

private theorem clmulAccumulateBit_oneHot_low {hot bitIdx : Nat}
    (acc : UInt64 × UInt64) (hhot : hot < 64) (hbitIdx : bitIdx < 64)
    (hsum : hot + bitIdx < 64) :
    clmulAccumulateBit acc ((1 : UInt64) <<< hot.toUInt64) bitIdx =
      (acc.1, acc.2 ^^^ ((1 : UInt64) <<< (hot + bitIdx).toUInt64)) := by
  by_cases hzero : bitIdx = 0
  · subst bitIdx
    simp [clmulAccumulateBit]
  · have hbitIdxPos : 0 < bitIdx := Nat.pos_of_ne_zero hzero
    simp [clmulAccumulateBit, hzero,
      oneHot_shiftLeft_of_sum_lt hhot hbitIdx hsum,
      oneHot_shiftRight_of_sum_lt hhot hbitIdx hbitIdxPos hsum]

private theorem clmulAccumulateBit_oneHot_high {hot bitIdx : Nat}
    (acc : UInt64 × UInt64) (hhot : hot < 64) (hbitIdx : bitIdx < 64)
    (hsum : 64 ≤ hot + bitIdx) :
    clmulAccumulateBit acc ((1 : UInt64) <<< hot.toUInt64) bitIdx =
      (acc.1 ^^^ ((1 : UInt64) <<< (hot + bitIdx - 64).toUInt64), acc.2) := by
  have hzero : bitIdx ≠ 0 := by omega
  simp [clmulAccumulateBit, hzero, oneHot_shiftLeft_of_sum_ge hhot hbitIdx hsum,
    oneHot_shiftRight_of_sum_ge hhot hbitIdx hsum]

private def clmulOneHotStep (a : UInt64) (hot : Nat) (acc : UInt64 × UInt64)
    (bitIdx : Nat) : UInt64 × UInt64 :=
  if (((((1 : UInt64) <<< hot.toUInt64) >>> bitIdx.toUInt64) &&& 1) != 0) then
    clmulAccumulateBit acc a bitIdx
  else
    acc

private theorem clmulOneHotStep_of_ne (a : UInt64) {hot bitIdx : Nat}
    (hhot : hot < 64) (hbitIdx : bitIdx < 64) (hne : hot ≠ bitIdx)
    (acc : UInt64 × UInt64) :
    clmulOneHotStep a hot acc bitIdx = acc := by
  have hclear :
      (((((1 : UInt64) <<< hot.toUInt64) >>> bitIdx.toUInt64) &&& 1) != 0) = false := by
    rw [oneHotWord_bit hhot hbitIdx]
    simp [hne]
  simp [clmulOneHotStep, hclear]

private theorem clmulOneHotStep_self (a : UInt64) {hot : Nat} (hhot : hot < 64)
    (acc : UInt64 × UInt64) :
    clmulOneHotStep a hot acc hot = clmulAccumulateBit acc a hot := by
  simp [clmulOneHotStep, GF2Poly.oneHotWord_bit_self hhot]

private theorem foldl_oneHot_absent (a : UInt64) {hot : Nat} (hhot : hot < 64)
    (acc : UInt64 × UInt64) :
    ∀ (xs : List Nat),
      hot ∉ xs →
      (∀ bitIdx ∈ xs, bitIdx < 64) →
      xs.foldl (clmulOneHotStep a hot) acc = acc := by
  intro xs
  induction xs generalizing acc with
  | nil =>
      intro _ _
      simp
  | cons bitIdx xs ih =>
      intro hnot hlt
      have hne : hot ≠ bitIdx := by
        intro h
        exact hnot (by simp [h])
      have hbitIdx : bitIdx < 64 := hlt bitIdx (by simp)
      have hnotTail : hot ∉ xs := by
        intro hmem
        exact hnot (by simp [hmem])
      have hltTail : ∀ idx ∈ xs, idx < 64 := by
        intro idx hmem
        exact hlt idx (by simp [hmem])
      rw [List.foldl_cons, clmulOneHotStep_of_ne a hhot hbitIdx hne acc]
      exact ih acc hnotTail hltTail

private theorem foldl_oneHot_list (a : UInt64) {hot : Nat} (hhot : hot < 64) :
    ∀ (xs : List Nat),
      xs.Nodup →
      (∀ bitIdx ∈ xs, bitIdx < 64) →
      xs.foldl (clmulOneHotStep a hot) (0, 0) =
        if hot ∈ xs then clmulAccumulateBit (0, 0) a hot else (0, 0) := by
  intro xs
  induction xs with
  | nil =>
      intro _ _
      simp
  | cons bitIdx xs ih =>
      intro hnodup hlt
      have hbitIdx : bitIdx < 64 := hlt bitIdx (by simp)
      have hltTail : ∀ idx ∈ xs, idx < 64 := by
        intro idx hmem
        exact hlt idx (by simp [hmem])
      by_cases hhit : bitIdx = hot
      · subst bitIdx
        have hnotTail : hot ∉ xs := by
          exact (List.nodup_cons.mp hnodup).1
        rw [List.foldl_cons, clmulOneHotStep_self a hhot]
        rw [foldl_oneHot_absent a hhot _ xs hnotTail hltTail]
        simp
      · have hstep :
            clmulOneHotStep a hot (0, 0) bitIdx = (0, 0) :=
          clmulOneHotStep_of_ne a hhot hbitIdx (Ne.symm hhit) (0, 0)
        rw [List.foldl_cons, hstep]
        have hnodupTail : xs.Nodup := (List.nodup_cons.mp hnodup).2
        rw [ih hnodupTail hltTail]
        have hhot_ne : hot ≠ bitIdx := Ne.symm hhit
        simp [hhot_ne]

private theorem foldl_oneHot (a : UInt64) {hot : Nat} (hhot : hot < 64) :
    (List.range 64).foldl
        (fun acc bitIdx =>
          if (((((1 : UInt64) <<< hot.toUInt64) >>> bitIdx.toUInt64) &&& 1) != 0) then
            clmulAccumulateBit acc a bitIdx
          else
            acc)
        (0, 0) =
      clmulAccumulateBit (0, 0) a hot := by
  change (List.range 64).foldl (clmulOneHotStep a hot) (0, 0) =
    clmulAccumulateBit (0, 0) a hot
  have hfold := foldl_oneHot_list (a := a) hhot (List.range 64)
    (List.nodup_range : (List.range 64).Nodup)
    (by
      intro bitIdx hmem
      exact List.mem_range.mp hmem)
  simpa [hhot] using hfold

/-- Carry-less multiplication by an in-word monomial has one contributing
partial product in the pure fold. -/
theorem pureClmul_oneHot (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    pureClmul a ((1 : UInt64) <<< bit.toUInt64) =
      if bit = 0 then (0, a) else (a >>> (64 - bit).toUInt64, a <<< bit.toUInt64) := by
  rw [pureClmul, foldl_oneHot a hbit, clmulAccumulateBit_zero]

/-- Trusted runtime hook for carry-less multiplication.

The compiled C shim must return the same `(hi, lo)` pair as `pureClmul`; the
intrinsic-backed implementations are an optimization only. -/
@[extern "lean_hex_clmul_u64"]
def clmul (a b : @& UInt64) : UInt64 × UInt64 :=
  pureClmul a b

/-- Runtime `clmul`, under its trusted reference contract, agrees with the
one-hot pure carry-less multiplication split. -/
theorem clmul_oneHot (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    clmul a ((1 : UInt64) <<< bit.toUInt64) =
      if bit = 0 then (0, a) else (a >>> (64 - bit).toUInt64, a <<< bit.toUInt64) := by
  rw [clmul, pureClmul_oneHot a hbit]

/-- High word of carry-less multiplication by an in-word monomial. -/
theorem clmul_oneHot_fst (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    (clmul a ((1 : UInt64) <<< bit.toUInt64)).1 =
      if bit = 0 then 0 else a >>> (64 - bit).toUInt64 := by
  rw [clmul_oneHot a hbit]
  by_cases h : bit = 0 <;> simp [h]

/-- Low word of carry-less multiplication by an in-word monomial. -/
theorem clmul_oneHot_snd (a : UInt64) {bit : Nat} (hbit : bit < 64) :
    (clmul a ((1 : UInt64) <<< bit.toUInt64)).2 =
      if bit = 0 then a else a <<< bit.toUInt64 := by
  rw [clmul_oneHot a hbit]
  by_cases h : bit = 0 <;> simp [h]

end Hex
