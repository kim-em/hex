import HexGfqField.Operations

/-!
Core conformance checks for the finite-field wrapper in `HexGfqField`.

Oracle: none
Mode: always
Covered operations:
- `ofQuotient`, `ofPoly`, and `repr`
- `zero` and `one`
- `add`, `mul`, `neg`, and `sub`
- `pow`
- `natCast`, `nsmul`, `intCast`, and `zsmul`
- `inv`, `div`, and `zpow`
- `frob`
Covered properties:
- finite-field representatives are reduced below the modulus degree
- field constructors and operations agree with quotient-ring reduction
- additive, multiplicative, and scalar ring laws are respected through
  the wrapper
- nonzero committed fixtures satisfy `x * x⁻¹ = 1`
- division agrees with multiplication by inverse
- Frobenius agrees with `p`-th power
- characteristic-`p` casts identify values modulo `p`
Covered edge cases:
- zero and one representatives
- already reduced linear representatives
- high-degree inputs reduced modulo `x^2 + x + 1` over `F_5`
- subtraction and negative integer representatives
- inverse, division, and negative powers on nonzero fixtures
-/

namespace Hex
namespace GFqField

private instance conformanceBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem prime_five : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

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

private abbrev Q := GFqRing.PolyQuotient modulus modulus_pos_degree
private abbrev F (hirr : FpPoly.Irreducible modulus) :=
  FiniteField modulus modulus_pos_degree prime_five hirr

private axiom modulus_irreducible : FpPoly.Irreducible modulus

private def q (coeffs : Array Nat) : Q :=
  GFqRing.ofPoly modulus modulus_pos_degree (polyFive coeffs)

private def ff (hirr : FpPoly.Irreducible modulus) (coeffs : Array Nat) : F hirr :=
  ofPoly modulus modulus_pos_degree prime_five hirr (polyFive coeffs)

private def reprNats {hirr : FpPoly.Irreducible modulus} (x : F hirr) : List Nat :=
  coeffNats (repr x)

private def conformanceChecks : Bool :=
  let hirr := modulus_irreducible
  let a : F hirr := ff hirr #[2, 3]
  let b : F hirr := ff hirr #[4, 1]
  let x : F hirr := ff hirr #[0, 1]
  let high : F hirr := ff hirr #[0, 0, 0, 1]
  [
    decide (reprNats (ofQuotient (q #[2, 3]) : F hirr) = [2, 3]),
    decide ((ofQuotient (q #[2, 3]) : F hirr).toQuotient = q #[2, 3]),
    decide (reprNats (ofQuotient (q #[0, 0, 0, 1]) : F hirr) = [1]),
    decide (reprNats (ofPoly modulus modulus_pos_degree prime_five hirr (polyFive #[2, 3])) = [2, 3]),
    decide (reprNats (ofPoly modulus modulus_pos_degree prime_five hirr (0 : FpPoly 5)) = []),
    decide (reprNats (ofPoly modulus modulus_pos_degree prime_five hirr (polyFive #[0, 0, 1])) =
      [4, 4]),
    decide (repr (ofPoly modulus modulus_pos_degree prime_five hirr (polyFive #[0, 0, 1])) =
      GFqRing.reduceMod modulus (polyFive #[0, 0, 1])),
    decide (reprNats a = [2, 3]),
    decide (reprNats (0 : F hirr) = []),
    decide (reprNats high = [1]),
    decide (reprNats (zero modulus modulus_pos_degree prime_five hirr) = []),
    decide (reprNats (0 : F hirr) = []),
    decide ((zero modulus modulus_pos_degree prime_five hirr : F hirr) =
      ofPoly modulus modulus_pos_degree prime_five hirr 0),
    decide (reprNats (one modulus modulus_pos_degree prime_five hirr) = [1]),
    decide (reprNats (1 : F hirr) = [1]),
    decide ((one modulus modulus_pos_degree prime_five hirr : F hirr) =
      ofPoly modulus modulus_pos_degree prime_five hirr 1),
    decide (reprNats (a + b) = [1, 4]),
    decide (reprNats (a + 0) = [2, 3]),
    decide (reprNats ((ff hirr #[0, 0, 1]) + b) = [3]),
    decide (repr (a + b) = GFqRing.reduceMod modulus (repr a + repr b)),
    decide (reprNats (a * b) = [0, 1]),
    decide (reprNats (a * 0) = []),
    decide (reprNats ((ff hirr #[0, 0, 1]) * x) = [1]),
    decide (repr (a * b) = GFqRing.reduceMod modulus (repr a * repr b)),
    decide (reprNats (-a) = [3, 2]),
    decide (reprNats (-(0 : F hirr)) = []),
    decide (reprNats (-(ff hirr #[0, 0, 1])) = [1, 1]),
    decide (reprNats (a - b) = [3, 2]),
    decide (reprNats ((0 : F hirr) - a) = [3, 2]),
    decide (reprNats (b - ff hirr #[0, 0, 1]) = [0, 2]),
    decide (reprNats (x ^ 0) = [1]),
    decide (reprNats (x ^ 2) = [4, 4]),
    decide (reprNats (x ^ 3) = [1]),
    decide (reprNats ((7 : Nat) : F hirr) = [2]),
    decide (reprNats ((0 : Nat) : F hirr) = []),
    decide (reprNats ((15 : Nat) : F hirr) = []),
    decide (((17 : Nat) : F hirr) = (2 : F hirr)),
    decide (reprNats (nsmul 3 x) = [0, 3]),
    decide (reprNats (nsmul 0 a) = []),
    decide (reprNats (nsmul 8 a) = [1, 4]),
    decide (reprNats ((-1 : Int) : F hirr) = [4]),
    decide (reprNats ((12 : Int) : F hirr) = [2]),
    decide (reprNats ((0 : Int) : F hirr) = []),
    decide (((-3 : Int) : F hirr) = (2 : F hirr)),
    decide (reprNats (zsmul (-2) x) = [0, 3]),
    decide (reprNats (zsmul 0 x) = []),
    decide (reprNats (zsmul 7 a) = [4, 1]),
    decide (reprNats a⁻¹ = [2, 1]),
    decide (reprNats b⁻¹ = [1, 3]),
    decide (reprNats x⁻¹ = [4, 4]),
    decide (a * a⁻¹ = 1),
    decide (b * b⁻¹ = 1),
    decide (x * x⁻¹ = 1),
    decide (reprNats (a / b) = [3]),
    decide (a / b = a * b⁻¹),
    decide (x / a = x * a⁻¹),
    decide ((0 : F hirr) / b = 0 * b⁻¹),
    decide (reprNats (zpow x (-1)) = [4, 4]),
    decide (reprNats (zpow b (-2)) = [2, 2]),
    decide (reprNats (zpow a 3) = reprNats (a ^ 3)),
    decide (reprNats (frob a) = [4, 2]),
    decide (reprNats (frob b) = [3, 4]),
    decide (reprNats (frob x) = [4, 4]),
    decide (frob a = a ^ (5 : Nat)),
    decide (frob b = b ^ (5 : Nat)),
    decide (frob x = x ^ (5 : Nat)),
    decide (FpPoly.degree (repr a) < FpPoly.degree modulus),
    decide (FpPoly.degree (repr (ff hirr #[0, 0, 1])) < FpPoly.degree modulus),
    decide (FpPoly.degree (repr (0 : F hirr)) < FpPoly.degree modulus),
    decide (GFqRing.reduceMod modulus (repr a) = repr a),
    decide (GFqRing.reduceMod modulus (repr (ff hirr #[0, 0, 1])) =
      repr (ff hirr #[0, 0, 1])),
    decide (GFqRing.reduceMod modulus (repr high) = repr high),
    decide (reprNats (0 + a) = reprNats a),
    decide (reprNats (a + 0) = reprNats a),
    decide (a + b = b + a),
    decide ((a + b) + x = a + (b + x)),
    decide (-a + a = 0),
    decide (a - b = a + -b),
    decide (reprNats (1 * a) = reprNats a),
    decide (reprNats (a * 1) = reprNats a),
    decide (a * b = b * a),
    decide ((a * b) * x = a * (b * x)),
    decide (a * (b + x) = a * b + a * x),
    decide ((a + b) * x = a * x + b * x),
    decide (nsmul 8 a = ((8 : Nat) : F hirr) * a),
    decide (zsmul 7 a = ((7 : Int) : F hirr) * a),
    decide (zsmul (-2) x = ((-2 : Int) : F hirr) * x)
  ].all id

#guard conformanceChecks

end GFqField
end Hex
