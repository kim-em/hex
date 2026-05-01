import HexArith.Montgomery.Redc

/-!
User-facing Montgomery modular arithmetic for `HexArith`.

This module exposes `MontCtx.mk`, conversion to and from Montgomery form,
Montgomery multiplication, and the `powMod` API that uses the Montgomery path
when the modulus is an odd `UInt64`.
-/

namespace MontCtx

/-- Double a reduced residue without leaving `UInt64` arithmetic. -/
private def doubleMod (p acc : UInt64) : UInt64 :=
  let gap := p - acc
  if acc ≥ gap then
    acc - gap
  else
    acc + acc

/-- Compute `R^2 mod p` by repeated doubling in native-word arithmetic. -/
private def r2Loop (p : UInt64) : Nat → UInt64 → UInt64
  | 0, acc => acc
  | n + 1, acc => r2Loop p n (doubleMod p acc)

/-- The `R^2 mod p` constant used to enter Montgomery form. -/
private def r2OfModulus (p : UInt64) : UInt64 :=
  if p ≤ 1 then
    0
  else
    let rModP := r2Loop p 64 1
    UInt64.ofNat ((rModP.toNat * rModP.toNat) % p.toNat)

/--
One `doubleMod` step doubles a canonical residue modulo `p`, using the
branch condition to avoid word overflow.
-/
private theorem toNat_doubleMod (p acc : UInt64) (hacc : acc.toNat < p.toNat) :
    (doubleMod p acc).toNat = (2 * acc.toNat) % p.toNat := by
  have hp_pos : 0 < p.toNat := by omega
  have hgap_toNat : (p - acc).toNat = p.toNat - acc.toNat :=
    UInt64.toNat_sub_of_le p acc (by
      rw [UInt64.le_iff_toNat_le]
      exact Nat.le_of_lt hacc)
  unfold doubleMod
  by_cases hbranch : p - acc ≤ acc
  · have hgap_le : p.toNat - acc.toNat ≤ acc.toNat := by
      simpa [UInt64.le_iff_toNat_le, hgap_toNat] using hbranch
    have hsub :
        (acc - (p - acc)).toNat = acc.toNat - (p.toNat - acc.toNat) := by
      simpa [hgap_toNat] using UInt64.toNat_sub_of_le acc (p - acc) hbranch
    have htwo_ge : p.toNat ≤ 2 * acc.toNat := by omega
    have htwo_lt : 2 * acc.toNat < 2 * p.toNat := by omega
    have hsub_lt : 2 * acc.toNat - p.toNat < p.toNat := by omega
    have hmod : (2 * acc.toNat) % p.toNat = 2 * acc.toNat - p.toNat := by
      calc
        (2 * acc.toNat) % p.toNat
            = (2 * acc.toNat - p.toNat) % p.toNat :=
              Nat.mod_eq_sub_mod htwo_ge
        _ = 2 * acc.toNat - p.toNat := Nat.mod_eq_of_lt hsub_lt
    simp [hbranch, hsub, hmod]
    omega
  · have hgap_gt : acc.toNat < p.toNat - acc.toNat := by
      have hnot : ¬ (p - acc).toNat ≤ acc.toNat := by
        intro hle
        exact hbranch (by
          rw [UInt64.le_iff_toNat_le]
          exact hle)
      omega
    have htwo_lt_p : 2 * acc.toNat < p.toNat := by omega
    have htwo_lt_word : 2 * acc.toNat < UInt64.word := by
      have hp_lt : p.toNat < UInt64.word := by
        simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size p
      omega
    have hadd : (acc + acc).toNat = 2 * acc.toNat := by
      rw [UInt64.toNat_add]
      rw [Nat.mod_eq_of_lt]
      · omega
      · simpa [UInt64.word, Nat.two_mul] using htwo_lt_word
    have hmod : (2 * acc.toNat) % p.toNat = 2 * acc.toNat :=
      Nat.mod_eq_of_lt htwo_lt_p
    simp [hbranch, hadd, hmod]

/-- The `r2Loop` accumulator equals repeated doubling modulo `p`. -/
private theorem toNat_r2Loop (p : UInt64) :
    ∀ n acc, acc.toNat < p.toNat →
      (r2Loop p n acc).toNat = (acc.toNat * 2 ^ n) % p.toNat := by
  intro n
  induction n with
  | zero =>
      intro acc hacc
      simp [r2Loop, Nat.mod_eq_of_lt hacc]
  | succ n ih =>
      intro acc hacc
      have hp_pos : 0 < p.toNat := by omega
      have hstep_eq := toNat_doubleMod p acc hacc
      have hstep_lt : (doubleMod p acc).toNat < p.toNat := by
        rw [hstep_eq]
        exact Nat.mod_lt _ hp_pos
      calc
        (r2Loop p (n + 1) acc).toNat
            = (r2Loop p n (doubleMod p acc)).toNat := by
              rfl
        _ = ((doubleMod p acc).toNat * 2 ^ n) % p.toNat := ih _ hstep_lt
        _ = (((2 * acc.toNat) % p.toNat) * 2 ^ n) % p.toNat := by
              rw [hstep_eq]
        _ = (acc.toNat * 2 ^ (n + 1)) % p.toNat := by
              rw [Nat.mod_mul_mod]
              congr 1
              rw [Nat.pow_succ]
              ac_rfl

/-- The executable `r2OfModulus` computes `R^2 mod p` for positive moduli. -/
private theorem toNat_r2OfModulus (p : UInt64) (hp_pos : 0 < p.toNat) :
    (r2OfModulus p).toNat = (UInt64.word * UInt64.word) % p.toNat := by
  have hp_lt_word : p.toNat < UInt64.word := by
    simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size p
  by_cases hle_one : p ≤ 1
  · have hp_le_one : p.toNat ≤ 1 := by
      have hle_nat : p.toNat ≤ (1 : UInt64).toNat := by
        simpa [UInt64.le_iff_toNat_le] using hle_one
      simpa using hle_nat
    have hp_eq_one : p.toNat = 1 := by omega
    unfold r2OfModulus
    simp [hle_one, hp_eq_one, Nat.mod_one]
  · have hp_gt_one : 1 < p.toNat := by
      have hnot_nat : ¬ p.toNat ≤ 1 := by
        intro hle
        exact hle_one (by
          rw [UInt64.le_iff_toNat_le]
          simpa using hle)
      omega
    have hloop :
        (r2Loop p 64 1).toNat = UInt64.word % p.toNat := by
      have hone_lt : (1 : UInt64).toNat < p.toNat := by
        simpa using hp_gt_one
      have h := toNat_r2Loop p 64 1 hone_lt
      simpa [UInt64.word, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using h
    have hsquare_lt : ((r2Loop p 64 1).toNat * (r2Loop p 64 1).toNat) % p.toNat <
        UInt64.word := by
      exact Nat.lt_trans (Nat.mod_lt _ hp_pos) hp_lt_word
    unfold r2OfModulus
    simp [hle_one]
    rw [Nat.mod_eq_of_lt]
    · rw [hloop, Nat.mod_mul_mod]
      calc
        UInt64.word * (UInt64.word % p.toNat) % p.toNat
            = (UInt64.word % p.toNat * ((UInt64.word % p.toNat) % p.toNat)) %
                p.toNat := Nat.mul_mod UInt64.word (UInt64.word % p.toNat) p.toNat
        _ = (UInt64.word % p.toNat * (UInt64.word % p.toNat)) % p.toNat := by
              rw [Nat.mod_mod]
        _ = UInt64.word * UInt64.word % p.toNat := by
              simp
    · simpa [UInt64.word] using hsquare_lt

/-- Build the executable Montgomery context for an odd `UInt64` modulus. -/
def mk (p : UInt64) (hp : p % 2 = 1) : MontCtx p :=
  { p_odd := hp
    p' := montInv p
    p'_eq := by
      have hp_nat : p.toNat % 2 = 1 := by
        have h := congrArg UInt64.toNat hp
        simpa [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt64.size] using h
      have hspec := montInv_spec p hp_nat
      simpa [UInt64.word, Nat.mul_comm] using hspec
    r2 := r2OfModulus p
    r2_eq := by
      have hp_nat : p.toNat % 2 = 1 := by
        have h := congrArg UInt64.toNat hp
        simpa [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt64.size] using h
      have hp_pos : 0 < p.toNat := by
        omega
      exact toNat_r2OfModulus p hp_pos }

/-- View the odd-modulus assumption as a Nat-level parity fact. -/
theorem p_odd_nat (ctx : MontCtx p) : p.toNat % 2 = 1 := by
  have h := congrArg UInt64.toNat ctx.p_odd
  simpa [UInt64.toNat_mod, UInt64.toNat_ofNat, UInt64.size] using h

/-- An odd `UInt64` modulus is positive at the Nat level. -/
theorem p_pos (ctx : MontCtx p) : 0 < p.toNat := by
  have hodd := ctx.p_odd_nat
  omega

/-- Every `UInt64` modulus is below the Montgomery radix `R = 2^64`. -/
theorem p_lt_R (_ctx : MontCtx p) : p.toNat < UInt64.word := by
  simpa [UInt64.word, UInt64.size] using UInt64.toNat_lt_size p

/-- Convert a standard residue into Montgomery form. -/
def toMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  redc ctx (UInt64.mulHi a ctx.r2) (a * ctx.r2)

/-- Convert a Montgomery residue back to the standard representation. -/
def fromMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  redc ctx 0 a

/-- Multiply two Montgomery residues, staying inside the Montgomery domain. -/
def mulMont (ctx : MontCtx p) (a b : UInt64) : UInt64 :=
  redc ctx (UInt64.mulHi a b) (a * b)

private theorem twoWordProduct_lt_p_word (ctx : MontCtx p) (a b : UInt64)
    (ha : a.toNat < p.toNat) (hb : b.toNat < p.toNat) :
    (a * b).toNat + (UInt64.mulHi a b).toNat * UInt64.word <
      p.toNat * UInt64.word := by
  have hprod_lt_p2 : a.toNat * b.toNat < p.toNat * p.toNat :=
    Nat.mul_lt_mul'' ha hb
  have hp2_lt_pword : p.toNat * p.toNat < p.toNat * UInt64.word :=
    Nat.mul_lt_mul_of_pos_left ctx.p_lt_R ctx.p_pos
  calc
    (a * b).toNat + (UInt64.mulHi a b).toNat * UInt64.word
        = (UInt64.mulHi a b).toNat * UInt64.word + (a * b).toNat := by
          rw [Nat.add_comm]
    _ = a.toNat * b.toNat := by
          exact UInt64.mulHi_mulLo a b
    _ < p.toNat * p.toNat := hprod_lt_p2
    _ < p.toNat * UInt64.word := hp2_lt_pword

/-- Montgomery conversion returns a canonical residue. -/
theorem toMont_lt (ctx : MontCtx p) (a : UInt64) (ha : a < p) :
    ctx.toMont a < p := by
  rw [UInt64.lt_iff_toNat_lt]
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hr2Nat : ctx.r2.toNat < p.toNat := by
    rw [ctx.r2_eq]
    exact Nat.mod_lt _ ctx.p_pos
  have hT := twoWordProduct_lt_p_word ctx a ctx.r2 haNat hr2Nat
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  unfold toMont
  rw [toNat_redc ctx (UInt64.mulHi a ctx.r2) (a * ctx.r2) hT]
  exact redcNat_lt ctx.p_pos ctx.p_lt_R hpp' hT

/-- Montgomery multiplication returns a canonical residue. -/
theorem mulMont_lt (ctx : MontCtx p) (a b : UInt64) (ha : a < p) (hb : b < p) :
    ctx.mulMont a b < p := by
  rw [UInt64.lt_iff_toNat_lt]
  have haNat : a.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using ha
  have hbNat : b.toNat < p.toNat := by
    simpa [UInt64.lt_iff_toNat_lt] using hb
  have hT := twoWordProduct_lt_p_word ctx a b haNat hbNat
  have hpp' : p.toNat * ctx.p'.toNat % UInt64.word = UInt64.word - 1 := by
    simpa [Nat.mul_comm] using ctx.p'_eq
  unfold mulMont
  rw [toNat_redc ctx (UInt64.mulHi a b) (a * b) hT]
  exact redcNat_lt ctx.p_pos ctx.p_lt_R hpp' hT

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

namespace HexArith

/-- Number of binary digits in a natural number. -/
private def bitLength (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 + 1

/-- Tail-recursive exponentiation by repeated squaring in Montgomery form. -/
private def powMontBitsGo (ctx : MontCtx p) (k : Nat) :
    Nat → Nat → UInt64 → UInt64 → UInt64
  | 0, _, acc, _ => acc
  | remaining + 1, bit, acc, base =>
      let acc' := if k.testBit bit then ctx.mulMont acc base else acc
      let base' := ctx.mulMont base base
      powMontBitsGo ctx k remaining (bit + 1) acc' base'

/-- Exponentiate a Montgomery-form base by repeated squaring. -/
private def powMont (ctx : MontCtx p) (base : UInt64) (n : Nat) : UInt64 :=
  powMontBitsGo ctx n (bitLength n) 0 (ctx.toMont 1) base

/-- Word-sized odd-modulus modular exponentiation via Montgomery arithmetic. -/
private def powModWordOdd (a n : Nat) (p : UInt64) (hp : p % 2 = 1) : Nat :=
  let ctx := MontCtx.mk p hp
  let base := ctx.toMont (UInt64.ofNat (a % p.toNat))
  (ctx.fromMont (powMont ctx base n)).toNat

/-- Nat-level fallback modular exponentiation by repeated squaring. -/
private def powModNat (a n p : Nat) : Nat :=
  let rec go (remaining bit acc base : Nat) : Nat :=
    match remaining with
    | 0 => acc
    | remaining' + 1 =>
        let acc' := if n.testBit bit then (acc * base) % p else acc
        let base' := (base * base) % p
        go remaining' (bit + 1) acc' base'
  go (bitLength n) 0 (1 % p) (a % p)

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
        powModNat a n p
    else
      powModNat a n p

/-- `powMod` agrees with ordinary modular exponentiation. -/
theorem powMod_eq (a n p : Nat) (hp : p > 0) :
    powMod a n p = a ^ n % p := by
  sorry

end HexArith
