import HexPolyFp.ModCompose

/-!
Square-free decomposition scaffolding for `FpPoly`.

This module packages a first executable square-free decomposition shell
for `HexPolyFp.FpPoly p`. The data layer records square-free factors
with multiplicities, exposes the reconstructed product, and provides a
Yun-style entry point built from the existing derivative, gcd, and
division scaffolds over `ZMod64 p` coefficients. The accompanying
theorems state the intended product, square-free, and pairwise-coprime
specification for later proof work.
-/

namespace HexPolyFp

namespace FpPoly

open HexModArith

variable {p : Nat} [NeZero p]

local instance instDecidableEqFpPoly : DecidableEq (FpPoly p) := by
  intro f g
  cases f with
  | mk coeffsF normalizedF =>
      cases g with
      | mk coeffsG normalizedG =>
          by_cases h : coeffsF = coeffsG
          · subst h
            exact isTrue rfl
          · exact isFalse (fun hfg => h (by cases hfg; rfl))

/-- One factor in a square-free decomposition together with its multiplicity. -/
structure SquareFreeFactor (p : Nat) [NeZero p] where
  factor : FpPoly p
  multiplicity : Nat

/-- The output of the square-free decomposition shell. -/
structure SquareFreeDecomposition (p : Nat) [NeZero p] where
  factors : Array (SquareFreeFactor p)

/-- The formal derivative of an `FpPoly`. -/
def formalDerivative (f : FpPoly p) : FpPoly p :=
  HexPoly.DensePoly.derivative (R := HexModArith.ZMod64 p) f

/--
Executable coefficient division for `ZMod64 p`.

The scaffold uses the partial inverse witness from `HexModArith` and
falls back to `0` on a nonunit divisor. Over prime moduli, later phases
show this agrees with true field division on nonzero coefficients.
-/
private def coeffDiv (a b : HexModArith.ZMod64 p) : HexModArith.ZMod64 p :=
  match HexModArith.ZMod64.inv? b with
  | some bInv => a * bInv
  | none => 0

/-- Polynomial division over `FpPoly` using the executable coefficient inverse shell. -/
private def divBy (f g : FpPoly p) : FpPoly p := by
  let _ : Div (HexModArith.ZMod64 p) := ⟨coeffDiv (p := p)⟩
  exact HexPoly.DensePoly.div (R := HexModArith.ZMod64 p) f g

/-- Polynomial gcd over `FpPoly` using the executable coefficient inverse shell. -/
private def gcd (f g : FpPoly p) : FpPoly p := by
  let _ : Div (HexModArith.ZMod64 p) := ⟨coeffDiv (p := p)⟩
  exact HexPoly.DensePoly.gcd (R := HexModArith.ZMod64 p) f g

/-- Repeated multiplication in `FpPoly`, used to rebuild factors by multiplicity. -/
private def pow (f : FpPoly p) : Nat → FpPoly p
  | 0 => C 1
  | n + 1 => mul (pow f n) f

/-- Expand one square-free factor by repeating it according to its multiplicity. -/
def SquareFreeFactor.expand (part : SquareFreeFactor p) : FpPoly p :=
  pow part.factor part.multiplicity

/-- The support of a square-free decomposition, forgetting multiplicities. -/
def SquareFreeDecomposition.support (decomp : SquareFreeDecomposition p) : Array (FpPoly p) :=
  decomp.factors.map SquareFreeFactor.factor

/-- Reconstruct the product represented by a square-free decomposition. -/
def SquareFreeDecomposition.product (decomp : SquareFreeDecomposition p) : FpPoly p :=
  decomp.factors.foldl (init := C 1) fun acc part => mul acc part.expand

/-- Two `FpPoly` values are coprime when their executable gcd shell is `1`. -/
def Coprime (f g : FpPoly p) : Prop :=
  gcd f g = C 1

/-- An `FpPoly` is square-free when it is coprime to its formal derivative. -/
def SquareFree (f : FpPoly p) : Prop :=
  Coprime f (formalDerivative f)

/-- Every factor in the decomposition is intended to be square-free. -/
def SquareFreeDecomposition.factorsSquareFree (decomp : SquareFreeDecomposition p) : Prop :=
  ∀ part ∈ decomp.factors.toList, SquareFree part.factor

/-- Distinct factors in the decomposition are intended to be pairwise coprime. -/
def SquareFreeDecomposition.pairwiseCoprime (decomp : SquareFreeDecomposition p) : Prop :=
  decomp.factors.toList.Pairwise fun a b => Coprime a.factor b.factor

/--
Yun-style square-free decomposition shell.

The executable branch separates the input into a square-free quotient
and a repeated-factor remainder using the existing derivative, gcd, and
division scaffolds. Cases that would require the later perfect-power
refinement currently fall back to a single-factor decomposition.
-/
def yunSquareFreeDecomposition (f : FpPoly p) : SquareFreeDecomposition p :=
  if _hf : f = 0 then
    { factors := #[] }
  else
    let deriv := formalDerivative f
    let shared := gcd f deriv
    let squareFreePart := divBy f shared
    if deriv = 0 ∨ shared = 0 ∨ shared = f ∨ squareFreePart = 0 then
      { factors := #[{ factor := f, multiplicity := 1 }] }
    else
      { factors := #[
          { factor := squareFreePart, multiplicity := 1 },
          { factor := shared, multiplicity := 2 }
        ] }

/-- Public alias for the executable square-free decomposition entry point. -/
def squareFreeDecomposition (f : FpPoly p) : SquareFreeDecomposition p :=
  yunSquareFreeDecomposition f

/-- The first square-free layer extracted from the decomposition shell. -/
def squareFreePart (f : FpPoly p) : FpPoly p :=
  match (squareFreeDecomposition f).factors.toList.head? with
  | some part => part.factor
  | none => 0

/-- The decomposition product recovers the input polynomial. -/
theorem squareFreeDecomposition_product (f : FpPoly p) :
    (squareFreeDecomposition f).product = f := by
  sorry

/-- Every recorded multiplicity is positive. -/
theorem squareFreeDecomposition_multiplicity_pos (f : FpPoly p) :
    ∀ part ∈ (squareFreeDecomposition f).factors.toList, 0 < part.multiplicity := by
  sorry

/-- The factors recorded by the decomposition are pairwise coprime. -/
theorem squareFreeDecomposition_pairwiseCoprime (f : FpPoly p) :
    (squareFreeDecomposition f).pairwiseCoprime := by
  sorry

/-- Every factor recorded by the decomposition is square-free. -/
theorem squareFreeDecomposition_factorsSquareFree (f : FpPoly p) :
    (squareFreeDecomposition f).factorsSquareFree := by
  sorry

/-- The extracted square-free part is square-free. -/
theorem squareFreePart_squareFree (f : FpPoly p) :
    SquareFree (squareFreePart f) := by
  sorry

end FpPoly

end HexPolyFp
