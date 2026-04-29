import HexHenselMathlib.Basic
import HexPolyMathlib.Basic

/-!
Mathlib-facing correctness and uniqueness theorem surface for executable
Hensel lifting.

The statements in this module transfer the `Hex.ZPoly` Hensel API through
`HexPolyMathlib.toPolynomial`, while keeping all new content proof-only.
-/

namespace HexHenselMathlib

open Polynomial

noncomputable section

/-- The iterative executable lift gives a factorization of `f` over Mathlib polynomials modulo `p^k`. -/
theorem hensel_correct
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    let φ := Int.castRingHom (ZMod (p ^ k))
    (HexPolyMathlib.toPolynomial r.g).map φ *
        (HexPolyMathlib.toPolynomial r.h).map φ =
      (HexPolyMathlib.toPolynomial f).map φ := by
  sorry

/-- The iterative executable lift extends the input factorization modulo `p`. -/
theorem hensel_extends
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    let φ := Int.castRingHom (ZMod p)
    (HexPolyMathlib.toPolynomial r.g).map φ =
        (HexPolyMathlib.toPolynomial g).map φ ∧
      (HexPolyMathlib.toPolynomial r.h).map φ =
        (HexPolyMathlib.toPolynomial h).map φ := by
  sorry

/-- The iterative executable lift preserves the Mathlib degree of the monic lifted factor. -/
theorem hensel_degree
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    (HexPolyMathlib.toPolynomial r.g).natDegree =
      (HexPolyMathlib.toPolynomial g).natDegree := by
  sorry

/-- Coprime monic factorizations with the same reduction modulo `p` are unique modulo `p^k`. -/
theorem hensel_unique (f g h g' h' : Polynomial ℤ) (p : ℕ) (k : ℕ)
    [Fact (Nat.Prime p)] (hk : 0 < k)
    (hg : g.Monic) (hg' : g'.Monic)
    (hdeg : g.natDegree = g'.natDegree)
    (hprod :
      let φ := Int.castRingHom (ZMod (p ^ k))
      (g.map φ) * (h.map φ) = f.map φ)
    (hprod' :
      let φ := Int.castRingHom (ZMod (p ^ k))
      (g'.map φ) * (h'.map φ) = f.map φ)
    (hg1 :
      let φ := Int.castRingHom (ZMod p)
      g.map φ = g'.map φ)
    (hh1 :
      let φ := Int.castRingHom (ZMod p)
      h.map φ = h'.map φ)
    (hcop :
      let φ := Int.castRingHom (ZMod p)
      IsCoprime (g.map φ) (h.map φ)) :
    let φ := Int.castRingHom (ZMod (p ^ k))
    g.map φ = g'.map φ ∧ h.map φ = h'.map φ := by
  sorry

end

end HexHenselMathlib
