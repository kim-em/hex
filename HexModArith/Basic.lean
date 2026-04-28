import HexArith.ExtGcd
import HexArith.Nat.ModArith
import HexArith.UInt64.Wide

/-!
Core `ZMod64` definitions for `hex-mod-arith`.

This module introduces the `UInt64`-backed residue type `Hex.ZMod64 p`
together with a project-local modulus-bounds typeclass, smart construction by
reduction mod `p`, the initial additive and multiplicative API, executable
exponentiation and inversion helpers, and the default extern-backed
multiplication contract.
-/
namespace Hex

namespace ZMod64

/-- `ZMod64 p` is only valid when `p` is positive and fits in one machine word. -/
class Bounds (p : Nat) : Prop where
  pPos : 0 < p
  pLeR : p ≤ UInt64.word

end ZMod64

/-- Residues mod `p` stored in a single machine word, with a proof of reduction. -/
structure ZMod64 (p : Nat) [ZMod64.Bounds p] where
  val : UInt64
  isLt : val.toNat < p

namespace ZMod64

variable {p : Nat} [Bounds p]

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

theorem normalize_lt (p n : Nat) [Bounds p] : normalize p n < p :=
  Nat.mod_lt _ (Bounds.pPos (p := p))

/--
Build a reduced residue by taking the Nat representative mod `p`.

The bound `p ≤ 2^64` ensures the reduced representative is stored faithfully in
the backing `UInt64`.
-/
def ofNat (p n : Nat) [Bounds p] : ZMod64 p := by
  let reduced := normalize p n
  have hred : reduced < p := normalize_lt p n
  have hword : reduced < UInt64.word := Nat.lt_of_lt_of_le hred (Bounds.pLeR (p := p))
  refine ⟨UInt64.ofNatLT reduced hword, ?_⟩
  simpa [reduced, UInt64.toNat_ofNatLT] using hred

@[simp] theorem toNat_ofNat (n : Nat) : (ofNat p n).toNat = n % p := by
  have hred : n % p < p := Nat.mod_lt _ (Bounds.pPos (p := p))
  have hword : n % p < UInt64.word := Nat.lt_of_lt_of_le hred (Bounds.pLeR (p := p))
  simp [ofNat, normalize, UInt64.toNat_ofNatLT]

@[simp] theorem val_toNat_ofNat (n : Nat) : (ofNat p n).val.toNat = n % p := by
  simpa using toNat_ofNat (p := p) n

/-- The zero residue class. -/
protected def zero : ZMod64 p :=
  ofNat p 0

/-- The residue class of one. -/
protected def one : ZMod64 p :=
  ofNat p 1

/-- Add two reduced residues and reduce the Nat sum mod `p`. -/
def add (a b : ZMod64 p) : ZMod64 p :=
  ofNat p (a.toNat + b.toNat)

/--
Subtract two residues by adding the modular complement of the second and
reducing mod `p`.
-/
def sub (a b : ZMod64 p) : ZMod64 p :=
  ofNat p (a.toNat + (p - b.toNat))

/--
Multiply two reduced residues and reduce the product mod `p`.

The trusted runtime contract is the `lean_hex_zmod64_mul` extern, whose C body
must agree with this pure Lean fallback.
-/
@[extern "lean_hex_zmod64_mul"]
def mul (a b : ZMod64 p) : ZMod64 p :=
  ofNat p (a.toNat * b.toNat)

/--
Raise a residue to a natural power using exponentiation by squaring.

The accumulator form keeps the executable path close to the intended downstream
runtime usage while preserving a simple semantic contract.
-/
def pow (a : ZMod64 p) (n : Nat) : ZMod64 p :=
  let rec go (base acc : ZMod64 p) (k : Nat) : ZMod64 p :=
    match k with
    | 0 => acc
    | m + 1 =>
        let acc' := if (m + 1) % 2 = 0 then acc else mul acc base
        go (mul base base) acc' ((m + 1) / 2)
  termination_by k
  decreasing_by
    simpa using Nat.div_lt_self (Nat.succ_pos m) (by decide : 1 < 2)
  go a ZMod64.one n

/--
Compute a modular inverse candidate via the integer extended-GCD helper from
`hex-arith`.

When `a` is coprime to `p`, this is the canonical inverse mod `p`; otherwise it
still exposes the executable Bezout-derived residue needed by later algebraic
layers.
-/
def inv (a : ZMod64 p) : ZMod64 p :=
  let (_, s, _) := Hex.pureIntExtGcd (Int.ofNat a.toNat) (Int.ofNat p)
  ofNat p (Int.toNat (s % Int.ofNat p))

instance : Zero (ZMod64 p) where
  zero := ZMod64.zero

instance : One (ZMod64 p) where
  one := ZMod64.one

instance : Add (ZMod64 p) where
  add := ZMod64.add

instance : Sub (ZMod64 p) where
  sub := ZMod64.sub

instance : Mul (ZMod64 p) where
  mul := ZMod64.mul

instance : Pow (ZMod64 p) Nat where
  pow := ZMod64.pow

instance : Inv (ZMod64 p) where
  inv := ZMod64.inv

@[simp] theorem toNat_zero : (ZMod64.zero : ZMod64 p).toNat = 0 := by
  rw [ZMod64.zero, toNat_ofNat]
  exact Nat.zero_mod _

@[simp] theorem toNat_one : (ZMod64.one : ZMod64 p).toNat = 1 % p := by
  rw [ZMod64.one, toNat_ofNat]

@[simp] theorem toNat_add (a b : ZMod64 p) :
    (add a b).toNat = (a.toNat + b.toNat) % p := by
  rw [add, toNat_ofNat]

@[simp] theorem toNat_sub (a b : ZMod64 p) :
    (sub a b).toNat = (a.toNat + (p - b.toNat)) % p := by
  rw [sub, toNat_ofNat]

@[simp] theorem toNat_mul (a b : ZMod64 p) :
    (mul a b).toNat = (a.toNat * b.toNat) % p := by
  rw [mul, toNat_ofNat]

@[simp] theorem toNat_inv_def (a : ZMod64 p) :
    (inv a).toNat =
      (Int.toNat ((let (_, s, _) := Hex.pureIntExtGcd (Int.ofNat a.toNat) (Int.ofNat p); s)
        % Int.ofNat p)) % p := by
  rw [inv, toNat_ofNat]

theorem toNat_pow (a : ZMod64 p) (n : Nat) :
    (pow a n).toNat = a.toNat ^ n % p := by
  sorry

theorem inv_mul_eq_one (a : ZMod64 p) (hcop : Nat.Coprime a.toNat p) :
    (mul (inv a) a).toNat = 1 % p := by
  sorry

theorem add_lt_modulus (a b : ZMod64 p) : (add a b).toNat < p := by
  simpa [toNat_add] using normalize_lt p (a.toNat + b.toNat)

theorem sub_lt_modulus (a b : ZMod64 p) : (sub a b).toNat < p := by
  simpa [toNat_sub] using normalize_lt p (a.toNat + (p - b.toNat))

theorem mul_lt_modulus (a b : ZMod64 p) : (mul a b).toNat < p := by
  simpa [toNat_mul] using normalize_lt p (a.toNat * b.toNat)

end ZMod64
end Hex
