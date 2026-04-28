import Std

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

/-- Trusted runtime hook for carry-less multiplication.

The compiled C shim must return the same `(hi, lo)` pair as `pureClmul`; the
intrinsic-backed implementations are an optimization only. -/
@[extern "lean_hex_clmul_u64"]
def clmul (a b : @& UInt64) : UInt64 × UInt64 :=
  pureClmul a b

end Hex
