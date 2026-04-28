import HexBerlekamp

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

end Conway

end Hex
