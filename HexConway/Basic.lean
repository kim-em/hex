import HexBerlekamp
import HexGfqRing.Basic

/-!
Tier 1 Conway-polynomial lookup support for `hex-conway`.

This module exposes the committed imported-table lookup
`luebeckConwayPolynomial?`, keeping the baseline Tier 1 story separate
from later Tier 2 Conway-compatibility proofs and Tier 3 search.
-/
namespace Hex

namespace Conway

instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩

/-- The committed Conway entry `C(2, 1) = X + 1` from the imported
Luebeck table. -/
def luebeckConwayPolynomial_2_1 : FpPoly 2 :=
  FpPoly.ofCoeffs #[1, 1]

/-- Tier 1 imported-table lookup for committed Luebeck Conway entries. -/
def luebeckConwayPolynomial? (p n : Nat) [ZMod64.Bounds p] : Option (FpPoly p) := by
  by_cases hp : p = 2
  · subst hp
    cases n with
    | zero => exact none
    | succ k =>
        cases k with
        | zero => exact some luebeckConwayPolynomial_2_1
        | succ _ => exact none
  · exact none

@[simp] theorem luebeckConwayPolynomial?_hit_2_1 :
    luebeckConwayPolynomial? 2 1 = some luebeckConwayPolynomial_2_1 :=
  rfl

@[simp] theorem luebeckConwayPolynomial?_miss_two_zero :
    luebeckConwayPolynomial? 2 0 = (none : Option (FpPoly 2)) :=
  rfl

@[simp] theorem luebeckConwayPolynomial?_miss_two_succ_succ (n : Nat) :
    luebeckConwayPolynomial? 2 (n + 2) = (none : Option (FpPoly 2)) := by
  cases n <;> rfl

@[simp] theorem luebeckConwayPolynomial?_miss_ne_two
    (p n : Nat) [ZMod64.Bounds p] (hp : p ≠ 2) :
    luebeckConwayPolynomial? p n = none := by
  simp [luebeckConwayPolynomial?, hp]

/-- The committed `C(2, 1)` entry is monic, so it can be fed to the
executable Rabin checker. -/
theorem luebeckConwayPolynomial_2_1_monic :
    DensePoly.Monic luebeckConwayPolynomial_2_1 := by
  rfl

/-- The committed `C(2, 1)` entry has positive degree. -/
theorem luebeckConwayPolynomial_2_1_degree_pos :
    0 < FpPoly.degree luebeckConwayPolynomial_2_1 := by
  decide

/-- The committed `C(2, 1)` entry is irreducible. -/
theorem luebeckConwayPolynomial_2_1_irreducible :
    FpPoly.Irreducible luebeckConwayPolynomial_2_1 := by
  sorry

/-- Every committed imported entry in the current Tier 1 slice comes with
an irreducibility witness. -/
theorem luebeckConwayPolynomial?_irreducible
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    FpPoly.Irreducible f := by
  by_cases hp : p = 2
  · subst hp
    cases n with
    | zero =>
        simp at h
    | succ k =>
        cases k with
        | zero =>
            have hf : f = luebeckConwayPolynomial_2_1 := by
              symm
              simpa [luebeckConwayPolynomial?_hit_2_1] using h
            subst hf
            exact luebeckConwayPolynomial_2_1_irreducible
        | succ j =>
            simp [luebeckConwayPolynomial?_miss_two_succ_succ] at h
  · simp [luebeckConwayPolynomial?, hp] at h

/-- A committed Conway entry packages the current Tier 1 lookup hit for a
supported `(p, n)` pair. -/
structure SupportedEntry (p n : Nat) [ZMod64.Bounds p] where
  poly : FpPoly p
  prime : Hex.Nat.Prime p
  isSupported : luebeckConwayPolynomial? p n = some poly

/-- The current committed table supports `C(2, 1)`. -/
def supportedEntry_2_1 : SupportedEntry 2 1 :=
  ⟨luebeckConwayPolynomial_2_1, by
    constructor
    · decide
    · intro m hm
      have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
      have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp at hm
      · exact Or.inl rfl
      · exact Or.inr rfl,
    rfl⟩

/-- Recover the committed Conway modulus for a supported entry. -/
def conwayPoly (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) : FpPoly p :=
  h.poly

@[simp] theorem luebeckConwayPolynomial?_conwayPoly
    {p n : Nat} [ZMod64.Bounds p] (h : SupportedEntry p n) :
    luebeckConwayPolynomial? p n = some (conwayPoly p n h) :=
  h.isSupported

/-- Every committed Tier 1 Conway entry in the current table is nonconstant. -/
theorem luebeckConwayPolynomial?_degree_pos
    {p n : Nat} [ZMod64.Bounds p] {f : FpPoly p}
    (h : luebeckConwayPolynomial? p n = some f) :
    0 < FpPoly.degree f := by
  by_cases hp : p = 2
  · subst hp
    cases n with
    | zero =>
        simp at h
    | succ k =>
        cases k with
        | zero =>
            have hf : f = luebeckConwayPolynomial_2_1 := by
              symm
              simpa [luebeckConwayPolynomial?_hit_2_1] using h
            subst hf
            exact luebeckConwayPolynomial_2_1_degree_pos
        | succ j =>
            simp [luebeckConwayPolynomial?_miss_two_succ_succ] at h
  · simp [luebeckConwayPolynomial?, hp] at h

/-- Supported Conway entries produce nonconstant moduli. -/
theorem conwayPoly_nonconstant
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    0 < FpPoly.degree (conwayPoly p n h) := by
  exact luebeckConwayPolynomial?_degree_pos
    (f := conwayPoly p n h) (luebeckConwayPolynomial?_conwayPoly h)

/-- Supported Conway entries carry the imported irreducibility witness. -/
theorem conwayPoly_irreducible
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    FpPoly.Irreducible (conwayPoly p n h) := by
  exact luebeckConwayPolynomial?_irreducible
    (f := conwayPoly p n h) (luebeckConwayPolynomial?_conwayPoly h)

end Conway

end Hex
