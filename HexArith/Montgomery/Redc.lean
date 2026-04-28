import HexArith.Montgomery.InvNat

/-!
Executable `UInt64` Montgomery reduction for `HexArith`.

This file packages the machine-word Montgomery parameters together with the
REDC bridge that consumes a two-word product `(Thi, Tlo)` and returns one
reduced residue.
-/

/-- Runtime Montgomery context for an odd `UInt64` modulus. -/
structure MontCtx (p : UInt64) where
  mkCtx ::
  p_odd : p % 2 = 1
  p' : UInt64
  p'_eq : (p'.toNat * p.toNat) % UInt64.word = UInt64.word - 1
  r2 : UInt64
  r2_eq : r2.toNat = (UInt64.word * UInt64.word) % p.toNat

/--
Executable Montgomery reduction from a two-word product `(Thi, Tlo)` encoded in
base `2^64`.
-/
def redc (ctx : MontCtx p) (Thi Tlo : UInt64) : UInt64 :=
  let m := Tlo * ctx.p'
  let (mhi, mlo) := UInt64.mulFull m p
  let (_, c1) := UInt64.addCarry Tlo mlo false
  let (addHi, c2) := UInt64.addCarry Thi mhi c1
  if c2 then
    addHi - p
  else if addHi ≥ p then
    addHi - p
  else
    addHi

/-- The low-word multiply computes the Montgomery correction factor `m`. -/
theorem redc_m_spec (ctx : MontCtx p) (Thi Tlo : UInt64) :
    let m := Tlo * ctx.p'
    m.toNat = (Tlo.toNat * ctx.p'.toNat) % UInt64.word := by
  sorry

/-- The carry pair `(c2, addHi)` represents the exact quotient `u`. -/
theorem redc_u_spec (ctx : MontCtx p) (Thi Tlo : UInt64) :
    let m := Tlo * ctx.p'
    let (_, c1) := UInt64.addCarry Tlo (m * p) false
    let (addHi, c2) := UInt64.addCarry Thi (UInt64.mulHi m p) c1
    addHi.toNat + c2.toNat * UInt64.word =
      (Tlo.toNat + Thi.toNat * UInt64.word + m.toNat * p.toNat) / UInt64.word := by
  sorry

/-- The final subtraction logic matches the Nat-level REDC normalization step. -/
theorem redc_sub_spec (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * UInt64.word < p.toNat * UInt64.word) :
    (redc ctx Thi Tlo).toNat =
      redcNat p.toNat ctx.p'.toNat (Tlo.toNat + Thi.toNat * UInt64.word) := by
  sorry

/-- The executable REDC bridge agrees with the Nat-level specification. -/
theorem toNat_redc (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * UInt64.word < p.toNat * UInt64.word) :
    (redc ctx Thi Tlo).toNat =
      redcNat p.toNat ctx.p'.toNat (Tlo.toNat + Thi.toNat * UInt64.word) := by
  exact redc_sub_spec ctx Thi Tlo hT
