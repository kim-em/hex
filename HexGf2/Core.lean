/-!
Packed `GF(2)` polynomial scaffolding.

This module provides the Phase 1 `GF2Poly` record shape together with the
pure-Lean carry-less multiply reference function and the public `clmul`
extern boundary used by later arithmetic layers.
-/

namespace Hex

/--
Pure-Lean carry-less multiplication on `UInt64`s.

The result is returned as the high and low 64-bit words of the full 128-bit
product over `GF(2)`.
-/
def pureClmul (a b : UInt64) : UInt64 × UInt64 := Id.run do
  let mut hi : UInt64 := 0
  let mut lo : UInt64 := 0
  for i in List.range 64 do
    let shift : UInt64 := .ofNat i
    if ((b >>> shift) &&& 1) != 0 then
      lo := lo ^^^ (a <<< shift)
      hi := hi ^^^ if i = 0 then (0 : UInt64) else a >>> (.ofNat (64 - i))
  pure (hi, lo)

end Hex

namespace HexGf2

/--
Polynomial over `GF(2)`, packed into 64-bit words.

Bit `j` of `words[i]` represents the coefficient of `x^(64*i + j)`.
-/
structure GF2Poly where
  words : Array UInt64
  degree : Nat
  wf : (words = #[] ∧ degree = 0) ∨
      (words.back! ≠ 0 ∧ degree < 64 * words.size ∧
        words[degree / 64]! &&& ((1 : UInt64) <<< (.ofNat (degree % 64))) ≠ 0 ∧
        ∀ i, degree < i → i < 64 * words.size →
          words[i / 64]! &&& ((1 : UInt64) <<< (.ofNat (i % 64))) = 0)

/--
Carry-less multiplication on packed 64-bit words.

The pure Lean body supplies the reference semantics used in proofs; the FFI
attachment replaces it at runtime when the C shim is available.
-/
@[extern "lean_hex_clmul_u64"]
def clmul (a b : @& UInt64) : UInt64 × UInt64 :=
  Hex.pureClmul a b

end HexGf2
