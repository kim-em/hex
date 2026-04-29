import HexGfqRing.Operations

/-!
Core conformance checks for the canonical quotient-ring surface in
`HexGfqRing`.

Oracle: none
Mode: always
Covered operations:
- `reduceMod`
- `ofPoly` and `repr`
- `zero`, `one`, and `const`
- `add`, `mul`, `neg`, and `sub`
- `pow`
- `natCast`, `nsmul`, `intCast`, and `zsmul`
- quotient-ring instance behavior over canonical representatives
Covered properties:
- quotient representatives are reduced below the modulus degree
- `repr (ofPoly f hf g)` agrees with `reduceMod f g`
- reducing an already reduced representative is idempotent
- quotient addition and multiplication agree with reducing polynomial sums
  and products
- additive and multiplicative ring identities, commutativity,
  associativity, distributivity, additive inverses, and subtraction are
  respected by canonical representatives
- natural and integer scalar multiplication agree with multiplication by
  the corresponding quotient constants
Covered edge cases:
- zero, one, and constant representatives
- already reduced linear representatives
- high-degree inputs reduced modulo `x^2 + x + 1` over `F_5`
- subtraction and negative integer representatives
- binary-shaped natural and integer scalar multipliers
-/

namespace Hex
namespace GFqRing

private instance conformanceBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def modulus : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5), 1, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem modulus_pos_degree : 0 < FpPoly.degree modulus := by
  decide

private abbrev Q := PolyQuotient modulus modulus_pos_degree

private def q (coeffs : Array Nat) : Q :=
  ofPoly modulus modulus_pos_degree (polyFive coeffs)

private def reprNats (x : Q) : List Nat :=
  coeffNats (repr x)

private def a : Q := q #[2, 3]
private def b : Q := q #[4, 1]
private def x : Q := q #[0, 1]
private def x2Raw : FpPoly 5 := polyFive #[0, 0, 1]
private def x2 : Q := ofPoly modulus modulus_pos_degree x2Raw
private def x3 : Q := q #[0, 0, 0, 1]

/-- info: [4, 4] -/
#guard_msgs in
#eval! coeffNats (reduceMod modulus x2Raw)

#guard coeffNats (reduceMod modulus (polyFive #[2, 3])) = [2, 3]
#guard coeffNats (reduceMod modulus (0 : FpPoly 5)) = []
#guard coeffNats (reduceMod modulus (polyFive #[0, 0, 0, 1])) = [1]

#guard reprNats (ofPoly modulus modulus_pos_degree (polyFive #[2, 3])) = [2, 3]
#guard reprNats (ofPoly modulus modulus_pos_degree (0 : FpPoly 5)) = []
#guard reprNats x2 = [4, 4]
#guard repr (ofPoly modulus modulus_pos_degree x2Raw) = reduceMod modulus x2Raw

#guard reprNats a = [2, 3]
#guard reprNats (0 : Q) = []
#guard reprNats x3 = [1]

#guard reprNats (zero modulus modulus_pos_degree) = []
#guard reprNats (0 : Q) = []
#guard zero modulus modulus_pos_degree = (ofPoly modulus modulus_pos_degree 0 : Q)

#guard reprNats (one modulus modulus_pos_degree) = [1]
#guard reprNats (1 : Q) = [1]
#guard one modulus modulus_pos_degree = (ofPoly modulus modulus_pos_degree 1 : Q)

#guard reprNats (const modulus modulus_pos_degree (ZMod64.ofNat 5 3)) = [3]
#guard reprNats (const modulus modulus_pos_degree (ZMod64.ofNat 5 0)) = []
#guard reprNats (const modulus modulus_pos_degree (ZMod64.ofNat 5 17)) = [2]

/-- info: [1, 4] -/
#guard_msgs in
#eval! reprNats (a + b)

#guard reprNats (a + 0) = [2, 3]
#guard reprNats (x2 + b) = [3]
#guard repr (a + b) = reduceMod modulus (repr a + repr b)

/-- info: [0, 1] -/
#guard_msgs in
#eval! reprNats (a * b)

#guard reprNats (a * 0) = []
#guard reprNats (x2 * x) = [1]
#guard repr (a * b) = reduceMod modulus (repr a * repr b)

#guard reprNats (-a) = [3, 2]
#guard reprNats (-(0 : Q)) = []
#guard reprNats (-x2) = [1, 1]

#guard reprNats (a - b) = [3, 2]
#guard reprNats ((0 : Q) - a) = [3, 2]
#guard reprNats (b - x2) = [0, 2]

#guard reprNats (x ^ 0) = [1]
#guard reprNats (x ^ 2) = [4, 4]
#guard reprNats (x ^ 3) = [1]

#guard reprNats ((7 : Nat) : Q) = [2]
#guard reprNats ((0 : Nat) : Q) = []
#guard reprNats ((15 : Nat) : Q) = []

#guard reprNats (nsmul 3 x) = [0, 3]
#guard reprNats (nsmul 0 a) = []
#guard reprNats (nsmul 8 a) = [1, 4]

#guard reprNats ((-1 : Int) : Q) = [4]
#guard reprNats ((12 : Int) : Q) = [2]
#guard reprNats ((0 : Int) : Q) = []

#guard reprNats (zsmul (-2) x) = [0, 3]
#guard reprNats (zsmul 0 x) = []
#guard reprNats (zsmul 7 a) = [4, 1]

#guard FpPoly.degree (repr a) < FpPoly.degree modulus
#guard FpPoly.degree (repr x2) < FpPoly.degree modulus
#guard FpPoly.degree (repr (0 : Q)) < FpPoly.degree modulus

#guard reduceMod modulus (repr a) = repr a
#guard reduceMod modulus (reduceMod modulus x2Raw) = reduceMod modulus x2Raw
#guard reduceMod modulus (repr x3) = repr x3

#guard reprNats (0 + a) = reprNats a
#guard reprNats (a + 0) = reprNats a
#guard a + b = b + a
#guard (a + b) + x = a + (b + x)
#guard -a + a = 0
#guard a - b = a + -b

#guard reprNats (1 * a) = reprNats a
#guard reprNats (a * 1) = reprNats a
#guard a * b = b * a
#guard (a * b) * x = a * (b * x)
#guard a * (b + x) = a * b + a * x
#guard (a + b) * x = a * x + b * x

#guard nsmul 8 a = ((8 : Nat) : Q) * a
#guard zsmul 7 a = ((7 : Int) : Q) * a
#guard zsmul (-2) x = ((-2 : Int) : Q) * x

end GFqRing
end Hex
