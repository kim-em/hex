import HexModArith
import HexPoly

/-!
`FpPoly` scaffolding over `ZMod64`.

This module introduces `HexPolyFp.FpPoly p` as dense polynomials with
`HexModArith.ZMod64 p` coefficients. It exposes thin wrappers for the
normalization-preserving constructors and basic arithmetic operations
from `HexPoly`, together with a fuel-bounded modular-power/Frobenius
surface built on monic reduction.
-/

namespace HexPolyFp

open HexModArith

/-- Canonical residues are decidable-equal via their stored representatives. -/
instance instDecidableEqZMod64 (p : Nat) : DecidableEq (HexModArith.ZMod64 p) := by
  intro a b
  by_cases h : a.val = b.val
  · exact isTrue (HexModArith.ZMod64.ext h)
  · exact isFalse (fun hab => h (congrArg HexModArith.ZMod64.val hab))

/-- Dense polynomials over the executable residue ring `ZMod64 p`. -/
abbrev FpPoly (p : Nat) [NeZero p] := HexPoly.DensePoly (HexModArith.ZMod64 p)

namespace FpPoly

variable {p : Nat} [NeZero p]

/-- Build an `FpPoly` from arbitrary coefficients by normalizing them. -/
def ofCoeffs (coeffs : Array (HexModArith.ZMod64 p)) : FpPoly p :=
  HexPoly.DensePoly.ofArray (R := HexModArith.ZMod64 p) coeffs

/-- The coefficient of `X^n`, defaulting to `0` past the support. -/
def coeff (f : FpPoly p) (n : Nat) : HexModArith.ZMod64 p :=
  HexPoly.DensePoly.coeff (R := HexModArith.ZMod64 p) f n

/-- The largest exponent with a stored nonzero coefficient, if any. -/
def natDegree? (f : FpPoly p) : Option Nat :=
  HexPoly.DensePoly.natDegree? (R := HexModArith.ZMod64 p) f

/-- The degree, with the zero polynomial convention `degree 0 = 0`. -/
def degree (f : FpPoly p) : Nat :=
  HexPoly.DensePoly.degree (R := HexModArith.ZMod64 p) f

/-- The leading coefficient, if the polynomial is nonzero. -/
def leadingCoeff? (f : FpPoly p) : Option (HexModArith.ZMod64 p) :=
  HexPoly.DensePoly.leadingCoeff? (R := HexModArith.ZMod64 p) f

/-- The constant polynomial with value `a`. -/
def C (a : HexModArith.ZMod64 p) : FpPoly p :=
  ofCoeffs #[a]

/-- The monomial `coeff * X^n`. -/
def monomial (coeff : HexModArith.ZMod64 p) (n : Nat) : FpPoly p :=
  ofCoeffs (((List.replicate n (0 : HexModArith.ZMod64 p)) ++ [coeff]).toArray)

/-- The polynomial variable `X`. -/
def X : FpPoly p :=
  monomial 1 1

/-- Addition on `FpPoly`. -/
def add (f g : FpPoly p) : FpPoly p :=
  HexPoly.DensePoly.add (R := HexModArith.ZMod64 p) f g

/-- Subtraction on `FpPoly`. -/
def sub (f g : FpPoly p) : FpPoly p :=
  HexPoly.DensePoly.sub (R := HexModArith.ZMod64 p) f g

/-- Schoolbook multiplication on `FpPoly`. -/
def mul (f g : FpPoly p) : FpPoly p :=
  HexPoly.DensePoly.mul (R := HexModArith.ZMod64 p) f g

/-- Reduce modulo a monic polynomial through the shared dense-polynomial API. -/
def modMonic (f modulus : FpPoly p) : FpPoly p :=
  HexPoly.DensePoly.modMonic (R := HexModArith.ZMod64 p) f modulus

/--
Fuel-bounded modular exponentiation by repeated squaring.

Later phases establish the expected semantics and sharpen the fuel bound.
-/
private def powModMonicAux (fuel : Nat) (base : FpPoly p) (exponent : Nat)
    (acc modulus : FpPoly p) : FpPoly p :=
  match fuel with
  | 0 => modMonic acc modulus
  | fuel + 1 =>
      if exponent = 0 then
        modMonic acc modulus
      else
        let acc' :=
          if exponent % 2 = 1 then
            modMonic (mul acc base) modulus
          else
            acc
        let base' := modMonic (mul base base) modulus
        powModMonicAux fuel base' (exponent / 2) acc' modulus

/--
Executable modular power entry point for downstream quotient-ring code.

The scaffold currently uses a simple fuel-bounded repeated-squaring shell
whose exponent control is refined in later phases.
-/
def powModMonic (base : FpPoly p) (n : Nat) (modulus : FpPoly p) : FpPoly p :=
  powModMonicAux (n + 1) (modMonic base modulus) n (C 1) modulus

/-- Frobenius action modulo a monic polynomial. -/
def frobeniusModMonic (f modulus : FpPoly p) : FpPoly p :=
  powModMonic f p modulus

/-- Iterate Frobenius `k` times modulo a monic polynomial. -/
def frobeniusPowModMonic (f modulus : FpPoly p) (k : Nat) : FpPoly p :=
  powModMonic f (p ^ k) modulus

end FpPoly

end HexPolyFp
