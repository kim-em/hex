import Init.Grind.Ring.Basic
import HexModArith.Basic

/-!
Ring-facing `ZMod64` API for `hex-mod-arith`.

This module adds the negation/cast surface around the executable `ZMod64`
operations and exposes the `Lean.Grind` semiring/ring/commutative-ring
instances expected by downstream libraries.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

private theorem neg_nonzero_toNat (a : ZMod64 p) {hpLt : p < UInt64.word}
    (hzero : a.val ≠ 0) :
    (-a.val - complementWord p hpLt).toNat = p - a.toNat := by
  have hzeroNat : a.toNat ≠ 0 := by
    intro h
    apply hzero
    apply UInt64.toNat_inj.mp
    simpa [toNat_eq_val] using h
  have hneg_toNat : (-a.val).toNat = UInt64.word - a.toNat := by
    rw [UInt64.toNat_neg]
    have hlt : UInt64.word - a.toNat < UInt64.word := by
      have hpos : 0 < a.toNat := Nat.pos_of_ne_zero hzeroNat
      omega
    rw [Nat.mod_eq_of_lt (by simpa [toNat_eq_val, UInt64.word, UInt64.size] using hlt)]
    simp [toNat_eq_val, UInt64.word, UInt64.size]
  have hge :
      UInt64.word ≤ UInt64.word - (UInt64.word - p) + (UInt64.word - a.toNat) := by
    have ha : a.toNat < p := a.isLt
    omega
  have hlt :
      UInt64.word - (UInt64.word - p) + (UInt64.word - a.toNat) -
          UInt64.word < UInt64.word := by
    have ha : a.toNat < p := a.isLt
    omega
  rw [UInt64.toNat_sub, hneg_toNat]
  simp [complementWord, UInt64.toNat_ofNatLT]
  rw [Nat.mod_eq_sub_mod (by simpa [UInt64.word] using hge),
    Nat.mod_eq_of_lt (by simpa [UInt64.word] using hlt)]
  have hfinal :
      UInt64.word - (UInt64.word - p) + (UInt64.word - a.toNat) - UInt64.word =
        p - a.toNat := by
    omega
  simpa [UInt64.word] using hfinal

private theorem neg_nonzero_lt (a : ZMod64 p) {hpLt : p < UInt64.word}
    (hzero : a.val ≠ 0) :
    (-a.val - complementWord p hpLt).toNat < p := by
  rw [neg_nonzero_toNat a hzero]
  have hzeroNat : a.toNat ≠ 0 := by
    intro h
    apply hzero
    apply UInt64.toNat_inj.mp
    simpa [toNat_eq_val] using h
  have ha : a.toNat < p := a.isLt
  omega

/-- The additive inverse represented by the complementary residue mod `p`. -/
def neg (a : ZMod64 p) : ZMod64 p := by
  by_cases hp : p = UInt64.word
  · refine ⟨-a.val, ?_⟩
    simpa [hp] using (UInt64.toNat_lt_size (-a.val))
  · have hpLt : p < UInt64.word := Nat.lt_of_le_of_ne (Bounds.pLeR (p := p)) hp
    let c64 := complementWord p hpLt
    by_cases hzero : a.val = 0
    · refine ⟨0, ?_⟩
      simp [Bounds.pPos (p := p)]
    · exact ⟨-a.val - c64, by simpa [c64] using neg_nonzero_lt a hzero⟩

/-- Natural-number literals in `ZMod64`. -/
def natCast (p : Nat) [Bounds p] (n : Nat) : ZMod64 p :=
  ofNat p n

/-- Natural scalar multiplication on `ZMod64`. -/
def nsmul (n : Nat) (a : ZMod64 p) : ZMod64 p :=
  ofNat p (n * a.toNat)

/-- Integer literals in `ZMod64`, reduced mod `p`. -/
def intCast (p : Nat) [Bounds p] : Int → ZMod64 p
  | .ofNat n => natCast p n
  | .negSucc n => neg (natCast p (n + 1))

/-- Integer scalar multiplication on `ZMod64`. -/
def zsmul (i : Int) (a : ZMod64 p) : ZMod64 p :=
  match i with
  | .ofNat n => nsmul n a
  | .negSucc n => neg (nsmul (n + 1) a)

instance : Neg (ZMod64 p) where
  neg := neg

instance : NatCast (ZMod64 p) where
  natCast := natCast p

instance (n : Nat) : OfNat (ZMod64 p) n where
  ofNat := natCast p n

instance : SMul Nat (ZMod64 p) where
  smul := nsmul

instance : IntCast (ZMod64 p) where
  intCast := intCast p

instance : SMul Int (ZMod64 p) where
  smul := zsmul

@[simp] theorem toNat_natCast (n : Nat) : (natCast p n).toNat = n % p := by
  rw [natCast, toNat_ofNat]

@[simp] theorem toNat_neg (a : ZMod64 p) : (neg a).toNat = (p - a.toNat) % p := by
  unfold neg
  by_cases hp : p = UInt64.word
  · rw [dif_pos hp]
    change (-a.val).toNat = (p - a.toNat) % p
    rw [UInt64.toNat_neg]
    simp [toNat_eq_val, hp, UInt64.word]
  · have hpLt : p < UInt64.word := Nat.lt_of_le_of_ne (Bounds.pLeR (p := p)) hp
    rw [dif_neg hp]
    by_cases hzero : a.val = 0
    · rw [dif_pos hzero]
      change (0 : UInt64).toNat = (p - a.toNat) % p
      have htoNat : a.toNat = 0 := by simp [toNat_eq_val, hzero]
      have hval : a.val.toNat = 0 := by simpa [toNat_eq_val] using htoNat
      simp [toNat_eq_val, hval]
    · rw [dif_neg hzero]
      change (-a.val - complementWord p hpLt).toNat = (p - a.toNat) % p
      rw [neg_nonzero_toNat a hzero]
      have hzeroNat : a.toNat ≠ 0 := by
        intro h
        apply hzero
        apply UInt64.toNat_inj.mp
        simpa [toNat_eq_val] using h
      have hlt : p - a.toNat < p := by
        have ha : a.toNat < p := a.isLt
        omega
      rw [Nat.mod_eq_of_lt hlt]

@[simp] theorem toNat_nsmul (n : Nat) (a : ZMod64 p) :
    (nsmul n a).toNat = (n * a.toNat) % p := by
  rw [nsmul, toNat_ofNat]

/-- Nat casts agree exactly when their representatives are congruent mod `p`. -/
theorem natCast_eq_natCast_iff (x y : Nat) :
    ((x : ZMod64 p) = y) ↔ x % p = y % p := by
  constructor
  · intro h
    simpa using congrArg ZMod64.toNat h
  · intro h
    apply ext
    apply UInt64.toNat_inj.mp
    simpa [toNat_natCast] using h

/-- A Nat literal vanishes in `ZMod64 p` exactly when `p` divides it. -/
theorem natCast_eq_zero_iff_dvd (n : Nat) : ((n : ZMod64 p) = 0) ↔ p ∣ n := by
  constructor
  · intro h
    exact Nat.dvd_of_mod_eq_zero ((natCast_eq_natCast_iff (p := p) n 0).mp h)
  · intro h
    exact (natCast_eq_natCast_iff (p := p) n 0).2 (Nat.mod_eq_zero_of_dvd h)

@[simp] theorem natCast_self : ((p : Nat) : ZMod64 p) = 0 := by
  exact (natCast_eq_natCast_iff (p := p) p 0).2 (by simp)

/-- The spec-level inverse law on canonical representatives. -/
theorem toNat_inv (a : ZMod64 p) (hcop : Nat.Coprime a.val.toNat p) :
    (a.inv * a).toNat = 1 % p := by
  simpa [ZMod64.toNat_eq_val] using inv_mul_eq_one (p := p) a hcop

instance : Lean.Grind.Semiring (ZMod64 p) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    ext
    sorry
  · intro a b
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a b c
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a
    ext
    sorry
  · intro a n
    ext
    sorry
  · intro n
    sorry
  · intro n
    sorry
  · intro n a
    sorry

instance : Lean.Grind.Ring (ZMod64 p) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    ext
    sorry
  · intro a b
    ext
    sorry
  · intro i a
    ext
    sorry
  · intro n a
    sorry
  · intro n
    sorry
  · intro i
    sorry

instance : Lean.Grind.CommRing (ZMod64 p) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  ext
  sorry

instance : Lean.Grind.IsCharP (ZMod64 p) p where
  ofNat_ext_iff {x y} := natCast_eq_natCast_iff (p := p) x y

end ZMod64

end Hex
