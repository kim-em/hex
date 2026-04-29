import HexModArith.Prime
import HexPolyFp.Basic

/-!
Executable square-free decomposition for `F_p[x]`.

This module implements a Yun-style square-free decomposition for
`Hex.FpPoly p`, recording the unit factor and the positive-multiplicity
square-free factors obtained from repeated gcd/derivative steps and
`p`-th-root descent in characteristic `p`. The public API carries an
explicit `Hex.Nat.Prime p` contract because the exported factorization and
square-free theorems are intended for prime-field coefficients.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]

/-- One square-free factor together with its multiplicity. -/
structure SquareFreeFactor (p : Nat) [ZMod64.Bounds p] where
  factor : FpPoly p
  multiplicity : Nat

/-- A square-free decomposition records the scalar unit and the nonconstant factors. -/
structure SquareFreeDecomposition (p : Nat) [ZMod64.Bounds p] where
  unit : ZMod64 p
  factors : List (SquareFreeFactor p)

/-- Detect the unit polynomial `1`. -/
private def isOne (f : FpPoly p) : Bool :=
  match f.degree? with
  | some 0 =>
      if f.coeff 0 = (1 : ZMod64 p) then
        true
      else
        false
  | _ => false

/-- Polynomial exponentiation uses square-and-multiply on the exponent bits. -/
private def pow (f : FpPoly p) (n : Nat) : FpPoly p :=
  let rec go (acc base : FpPoly p) (k : Nat) : FpPoly p :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then acc * base else acc
      go acc' (base * base) (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go 1 f n

/-- Multiply the factors in a square-free decomposition with their multiplicities. -/
def weightedProduct (factors : List (SquareFreeFactor p)) : FpPoly p :=
  factors.foldl (fun acc sf => acc * pow sf.factor sf.multiplicity) 1

/--
Extract the formal `p`-th root by keeping exactly the coefficients whose
degrees are multiples of `p`.
-/
private def pthRoot (f : FpPoly p) : FpPoly p :=
  let rootSize := (f.size + p - 1) / p
  ofCoeffs <|
    (List.range rootSize).map (fun i => f.coeff (i * p)) |>.toArray

/-- Split off the leading coefficient so the recursive Yun loop can work on a monic input. -/
private def normalizeMonic (f : FpPoly p) : ZMod64 p × FpPoly p :=
  if f.isZero then
    (0, 0)
  else
    let unit := DensePoly.leadingCoeff f
    (unit, DensePoly.scale unit⁻¹ f)

/--
Yun's inner loop: peel off the factors with multiplicities `i`, `i + 1`, ...
from the coprime/repeated split `(c, w)`.
-/
private def yunFactors
    (c w : FpPoly p) (i : Nat) (fuel : Nat)
    (acc : List (SquareFreeFactor p)) :
    List (SquareFreeFactor p) × FpPoly p :=
  match fuel with
  | 0 => (acc, w)
  | fuel + 1 =>
      if isOne c then
        (acc, w)
      else
        let y := DensePoly.gcd c w
        let z := c / y
        let acc' :=
          if isOne z then
            acc
          else
            acc ++ [{ factor := z, multiplicity := i }]
        yunFactors y (w / y) (i + 1) fuel acc'

/--
Recursive square-free decomposition over `F_p[x]`. A derivative-zero branch
descends through the formal `p`-th root and scales multiplicities by `p`.
-/
private def squareFreeAux (f : FpPoly p) (multiplicity : Nat) :
    Nat → List (SquareFreeFactor p)
  | 0 => []
  | fuel + 1 =>
      if f.isZero then
        []
      else
        let df := DensePoly.derivative f
        if df.isZero then
          squareFreeAux (pthRoot f) (multiplicity * p) fuel
        else
          let g := DensePoly.gcd f df
          let c := f / g
          let loop := yunFactors c g multiplicity fuel []
          let factors := loop.1
          let repeated := loop.2
          if isOne repeated then
            factors
          else
            factors ++ squareFreeAux (pthRoot repeated) (multiplicity * p) fuel

/--
Compute a square-free decomposition by normalizing away the leading scalar and
running Yun's algorithm on the resulting monic polynomial.
-/
def squareFreeDecomposition (hp : Hex.Nat.Prime p) (f : FpPoly p) : SquareFreeDecomposition p :=
  let _ := hp
  let normalized := normalizeMonic f
  let unit := normalized.1
  let monicPart := normalized.2
  let factors := squareFreeAux monicPart 1 (monicPart.size + 1)
  { unit, factors }

theorem squareFree_pairwise_coprime (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    d.factors.Pairwise (fun a b => DensePoly.gcd a.factor b.factor = 1) := by
  sorry

theorem squareFree_weightedProduct (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    DensePoly.C d.unit * weightedProduct d.factors = f := by
  sorry

theorem squareFree_factors_squareFree (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    let d := squareFreeDecomposition hp f
    ∀ sf ∈ d.factors, DensePoly.gcd sf.factor (DensePoly.derivative sf.factor) = 1 := by
  sorry

end FpPoly
end Hex
