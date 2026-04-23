import HexArith.Montgomery.Context

/-!
`UInt64` Montgomery REDC scaffolding.

This module provides the Phase 1 executable Montgomery REDC bridge and
its key specification statements for the arithmetic library.
-/

namespace HexArith

namespace MontCtx

/--
Executable single-word Montgomery REDC.

The input is represented as the 128-bit value
`Tlo.toNat + Thi.toNat * montgomeryRadix`, split into high and low
`UInt64` words.
-/
def redc (ctx : MontCtx p) (Thi Tlo : UInt64) : UInt64 :=
  let m := Tlo * ctx.p'
  let (_, c1) := UInt64.addCarry Tlo (m * p) false
  let (addHi, c2) := UInt64.addCarry Thi (UInt64.mulHi m p) c1
  if c2 then addHi - p
  else if addHi ≥ p then addHi - p else addHi

/-- The low-word multiply computes the expected Montgomery mask. -/
theorem redc_m_spec (ctx : MontCtx p) (Thi Tlo : UInt64) :
    let m := Tlo * ctx.p'
    m.toNat = (Tlo.toNat * ctx.p'.toNat) % montgomeryRadix := by
  sorry

/--
The carry/high-word pair produced by the REDC additions encodes the
intermediate quotient `u = (T + m * p) / R`.
-/
theorem redc_u_spec (ctx : MontCtx p) (Thi Tlo : UInt64) :
    let m := Tlo * ctx.p'
    let (_, c1) := UInt64.addCarry Tlo (m * p) false
    let (addHi, c2) := UInt64.addCarry Thi (UInt64.mulHi m p) c1
    addHi.toNat + c2.toNat * montgomeryRadix =
      (Tlo.toNat + Thi.toNat * montgomeryRadix + m.toNat * p.toNat) / montgomeryRadix := by
  sorry

/-- The executable subtraction branch agrees with the Nat-level REDC step. -/
theorem redc_sub_spec (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * montgomeryRadix < p.toNat * montgomeryRadix) :
    (ctx.redc Thi Tlo).toNat =
      redcNat p.toNat ctx.p'.toNat (Tlo.toNat + Thi.toNat * montgomeryRadix) := by
  sorry

/-- The `UInt64` REDC bridge refines the pure Nat REDC definition. -/
theorem toNat_redc (ctx : MontCtx p) (Thi Tlo : UInt64)
    (hT : Tlo.toNat + Thi.toNat * montgomeryRadix < p.toNat * montgomeryRadix) :
    (ctx.redc Thi Tlo).toNat =
      redcNat p.toNat ctx.p'.toNat (Tlo.toNat + Thi.toNat * montgomeryRadix) := by
  simpa using ctx.redc_sub_spec Thi Tlo hT

end MontCtx
end HexArith
