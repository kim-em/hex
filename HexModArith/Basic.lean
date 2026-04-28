import HexArith.Nat.ModArith
import HexArith.UInt64.Wide

/-!
Core `ZMod64` definitions for `hex-mod-arith`.

This module introduces the `UInt64`-backed residue type `Hex.ZMod64 p`
together with smart construction by reduction mod `p`, basic coercions and
accessors, and the initial additive API. The executable operations are defined
via Nat-level reduction so values stay canonically reduced while later phases
swap in specialized multiplication backends from `HexArith`.
-/
namespace Hex

/-- Residues mod `p` stored in a single machine word, with a proof of reduction. -/
structure ZMod64 (p : Nat) where
  val : UInt64
  isLt : val.toNat < p

namespace ZMod64

variable {p : Nat}

/-- View a residue as its reduced Nat representative. -/
def toNat (a : ZMod64 p) : Nat :=
  a.val.toNat

/-- View a residue as its underlying `UInt64` word. -/
def toUInt64 (a : ZMod64 p) : UInt64 :=
  a.val

instance : CoeOut (ZMod64 p) UInt64 where
  coe := toUInt64

instance : CoeOut (ZMod64 p) Nat where
  coe := toNat

@[simp] theorem toUInt64_eq_val (a : ZMod64 p) : a.toUInt64 = a.val := rfl
@[simp] theorem toNat_eq_val (a : ZMod64 p) : a.toNat = a.val.toNat := rfl
@[simp] theorem toNat_lt (a : ZMod64 p) : a.toNat < p := a.isLt

@[ext] theorem ext {a b : ZMod64 p} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Reduce a Nat representative modulo `p`. -/
def normalize (p n : Nat) : Nat :=
  n % p

theorem normalize_lt (hp : 0 < p) (n : Nat) : normalize p n < p :=
  Nat.mod_lt _ hp

/--
Build a reduced residue by taking the Nat representative mod `p`.

The bound `p ≤ 2^64` ensures the reduced representative is stored faithfully in
the backing `UInt64`.
-/
def ofNat (p n : Nat) (hp : 0 < p) (hword : p ≤ UInt64.word) : ZMod64 p := by
  let reduced := normalize p n
  have hred : reduced < p := normalize_lt hp n
  have hword' : reduced < UInt64.word := Nat.lt_of_lt_of_le hred hword
  refine ⟨UInt64.ofNatLT reduced hword', ?_⟩
  simpa [UInt64.toNat_ofNatLT] using hred

@[simp] theorem toNat_ofNat (n : Nat) (hp : 0 < p) (hword : p ≤ UInt64.word) :
    (ofNat p n hp hword).toNat = n % p := by
  have hred : n % p < p := Nat.mod_lt _ hp
  have hword' : n % p < UInt64.word := Nat.lt_of_lt_of_le hred hword
  simp [ofNat, normalize, UInt64.toNat_ofNatLT]

@[simp] theorem val_toNat_ofNat (n : Nat) (hp : 0 < p) (hword : p ≤ UInt64.word) :
    (ofNat p n hp hword).val.toNat = n % p := by
  simpa using toNat_ofNat (p := p) n hp hword

section BasicOps

variable (hp : 0 < p) (hword : p ≤ UInt64.word)

/-- The zero residue class. -/
protected def zero : ZMod64 p :=
  ofNat p 0 hp hword

/-- The residue class of one. -/
protected def one : ZMod64 p :=
  ofNat p 1 hp hword

/-- Add two reduced residues and reduce the Nat sum mod `p`. -/
def add (a b : ZMod64 p) : ZMod64 p :=
  ofNat p (a.toNat + b.toNat) hp hword

/--
Subtract two residues by adding the modular complement of the second and
reducing mod `p`.
-/
def sub (a b : ZMod64 p) : ZMod64 p :=
  ofNat p (a.toNat + (p - b.toNat)) hp hword

@[simp] theorem toNat_zero :
    (ZMod64.zero hp hword).toNat = 0 := by
  rw [ZMod64.zero, toNat_ofNat]
  exact Nat.zero_mod _

@[simp] theorem toNat_one :
    (ZMod64.one hp hword).toNat = 1 % p := by
  rw [ZMod64.one, toNat_ofNat]

@[simp] theorem toNat_add (a b : ZMod64 p) :
    (add hp hword a b).toNat = (a.toNat + b.toNat) % p := by
  rw [add, toNat_ofNat]

@[simp] theorem toNat_sub (a b : ZMod64 p) :
    (sub hp hword a b).toNat = (a.toNat + (p - b.toNat)) % p := by
  rw [sub, toNat_ofNat]

theorem add_lt_modulus (a b : ZMod64 p) : (add hp hword a b).toNat < p := by
  simpa [toNat_add] using normalize_lt hp (a.toNat + b.toNat)

theorem sub_lt_modulus (a b : ZMod64 p) : (sub hp hword a b).toNat < p := by
  simpa [toNat_sub] using normalize_lt hp (a.toNat + (p - b.toNat))

end BasicOps
end ZMod64
end Hex
