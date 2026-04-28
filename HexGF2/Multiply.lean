import HexGF2.Basic
import HexGF2.Clmul

/-!
Packed `GF2Poly` multiplication.

This module lifts the carry-less `UInt64` primitive to polynomial
multiplication on packed `GF(2)` coefficients. Each word pair contributes a
128-bit carry-less product, which is XOR-accumulated into the result words and
then normalized back into the `GF2Poly` invariant.
-/
namespace Hex
namespace GF2Poly

/-- XOR a 128-bit carry-less product into adjacent result words. -/
private def xorClmulAt (acc : Array UInt64) (idx : Nat) (x y : UInt64) : Array UInt64 :=
  let (hi, lo) := clmul x y
  let acc := acc.set! idx (acc[idx]! ^^^ lo)
  acc.set! (idx + 1) (acc[idx + 1]! ^^^ hi)

/-- Raw packed-word multiplication before trailing zero normalization. -/
private def mulWords (xs ys : Array UInt64) : Array UInt64 :=
  if xs.isEmpty || ys.isEmpty then
    #[]
  else
    (List.range xs.size).foldl
      (fun acc i =>
        let x := xs[i]!
        (List.range ys.size).foldl
          (fun acc j => xorClmulAt acc (i + j) x ys[j]!)
          acc)
      (Array.replicate (xs.size + ys.size) (0 : UInt64))

/-- Multiplication in `F_2[x]` via carry-less word products and XOR
accumulation. -/
def mul (p q : GF2Poly) : GF2Poly :=
  ofWords (mulWords p.words q.words)

instance : Mul GF2Poly where
  mul := mul

/-- The normalized product stores no more than the raw convolution capacity. -/
theorem wordCount_mul_le (p q : GF2Poly) : (p * q).wordCount ≤ p.wordCount + q.wordCount := by
  sorry

end GF2Poly
end Hex
