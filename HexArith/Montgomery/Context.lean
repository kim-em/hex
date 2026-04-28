import Mathlib.Data.Nat.BinaryRec
import HexArith.Montgomery.Redc

/-!
User-facing Montgomery modular arithmetic for `HexArith`.

This module exposes `MontCtx.mk`, conversion to and from Montgomery form,
Montgomery multiplication, and the `powMod` API that uses the Montgomery path
when the modulus is an odd `UInt64`.
-/

namespace MontCtx

/-- Compute `R^2 mod p` by repeated doubling at the Nat level. -/
private def r2Loop (p : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => r2Loop p n ((acc + acc) % p)

/-- The `R^2 mod p` constant used to enter Montgomery form. -/
private def r2OfModulus (p : UInt64) : UInt64 :=
  if _hp : p.toNat = 0 then
    0
  else
    UInt64.ofNat (r2Loop p.toNat 128 (1 % p.toNat))

/-- Build the executable Montgomery context for an odd `UInt64` modulus. -/
def mk (p : UInt64) (hp : p % 2 = 1) : MontCtx p :=
  { p_odd := hp
    p' := montInv p
    p'_eq := by
      sorry
    r2 := r2OfModulus p
    r2_eq := by
      sorry }

/-- View the odd-modulus assumption as a Nat-level parity fact. -/
theorem p_odd_nat (ctx : MontCtx p) : p.toNat % 2 = 1 := by
  sorry

/-- An odd `UInt64` modulus is positive at the Nat level. -/
theorem p_pos (ctx : MontCtx p) : 0 < p.toNat := by
  sorry

/-- Every `UInt64` modulus is below the Montgomery radix `R = 2^64`. -/
theorem p_lt_R (ctx : MontCtx p) : p.toNat < UInt64.word := by
  sorry

/-- Convert a standard residue into Montgomery form. -/
def toMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  redc ctx (UInt64.mulHi a ctx.r2) (a * ctx.r2)

/-- Convert a Montgomery residue back to the standard representation. -/
def fromMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  redc ctx 0 a

/-- Multiply two Montgomery residues, staying inside the Montgomery domain. -/
def mulMont (ctx : MontCtx p) (a b : UInt64) : UInt64 :=
  redc ctx (UInt64.mulHi a b) (a * b)

/-- Montgomery conversion returns a canonical residue. -/
theorem toMont_lt (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    ctx.toMont a < p := by
  sorry

/-- Montgomery multiplication returns a canonical residue. -/
theorem mulMont_lt (ctx : MontCtx p) (a b : UInt64) (ha : a < p) (hb : b < p) :
    ctx.mulMont a b < p := by
  sorry

/-- Montgomery multiplication preserves the represented residue product. -/
theorem mulMont_repr (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont a b)).toNat =
      ((ctx.fromMont a).toNat * (ctx.fromMont b).toNat) % p.toNat := by
  sorry

/-- Converting into Montgomery form and back is the identity on reduced inputs. -/
theorem fromMont_toMont (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    ctx.fromMont (ctx.toMont a) = a := by
  sorry

/-- Montgomery multiplication computes modular multiplication after conversion. -/
theorem toNat_mulMont (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat := by
  sorry

/-- User-facing equality form of Montgomery multiplication. -/
theorem mulMont_eq (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b)) =
      UInt64.ofNat ((a.toNat * b.toNat) % p.toNat) := by
  sorry

end MontCtx

/-- Tail-recursive exponentiation by repeated squaring in Montgomery form. -/
private def powMontGo (ctx : MontCtx p) (k : Nat) : UInt64 → UInt64 → UInt64 :=
  Nat.binaryRec
    (fun acc _ => acc)
    (fun bit _ rec acc base =>
      rec (cond bit (ctx.mulMont acc base) acc) (ctx.mulMont base base))
    k

/-- Exponentiate a Montgomery-form base by repeated squaring. -/
private def powMont (ctx : MontCtx p) (base : UInt64) (n : Nat) : UInt64 :=
  powMontGo ctx n (ctx.toMont 1) base

/-- Word-sized odd-modulus modular exponentiation via Montgomery arithmetic. -/
private def powModWordOdd (a n : Nat) (p : UInt64) (hp : p % 2 = 1) : Nat :=
  let ctx := MontCtx.mk p hp
  let base := ctx.toMont (UInt64.ofNat (a % p.toNat))
  (ctx.fromMont (powMont ctx base n)).toNat

/--
Modular exponentiation by repeated squaring, using Montgomery arithmetic for
odd `UInt64` moduli and a direct Nat fallback otherwise.
-/
def powMod (a n p : Nat) : Nat :=
  if _hp0 : p = 0 then
    0
  else
    let p64 := UInt64.ofNat p
    if _hfit : p64.toNat = p then
      if hodd : p64 % 2 = 1 then
        powModWordOdd a n p64 hodd
      else
        a ^ n % p
    else
      a ^ n % p

/-- `powMod` agrees with ordinary modular exponentiation. -/
theorem powMod_eq (a n p : Nat) (hp : p > 0) :
    powMod a n p = a ^ n % p := by
  sorry
