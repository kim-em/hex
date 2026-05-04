import Hex.Conformance.Emit
import HexPoly

/-!
JSONL emit driver for the `hex-poly` oracle.

`lake exe hexpoly_emit_fixtures` writes one JSONL record per fixture
followed by one `result` record per Lean-side computed value to
`stdout` (or to `$HEX_FIXTURE_OUTPUT` when set).  The companion
oracle driver `scripts/oracle/poly_flint.py` reads the same stream
and re-runs each operation through python-flint for cross-check.

The fixture set is committed and intentionally small: this bootstrap
covers `mul` and (exact) `divmod` over `Hex.DensePoly Int`, where the
Lean answer matches python-flint's `fmpz_poly` exactly.  `gcd`
cross-checks are deferred to the per-library oracle issue (#1987)
because `Hex.DensePoly Int.gcd` runs Euclidean reduction with
truncating integer division, so it does not match `fmpz_poly.gcd`'s
primitive associate; the right fix is rational fixtures, not a hack
in the bootstrap.  Coordinate any future case-id additions with the
`HexPoly` Conformance module so identical ids stay in sync.
-/

namespace Hex.PolyEmit

open Hex.Conformance.Emit
open Hex.DensePoly

private def lib : String := "HexPoly"

/-- A `mul` fixture: emits both factor cases plus the product result. -/
private structure MulCase where
  id     : String
  left   : List Int
  right  : List Int

private def mulCases : List MulCase := [
  { id := "mul/typical",
    left  := [3, 0, -2],
    right := [-1, 5, 2] },
  { id := "mul/byOne",
    left  := [3, 0, -2],
    right := [1] },
  { id := "mul/zero",
    left  := [],
    right := [0, 4, 0, -5] },
  { id := "mul/sparseShift",
    left  := [0, 4, 0, -5],
    right := [0, 0, 0, -2] }
]

private def emitMulCase (c : MulCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left")  c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  let p : DensePoly Int := ofCoeffs c.left.toArray
  let q : DensePoly Int := ofCoeffs c.right.toArray
  let prod : DensePoly Int := p * q
  emitResult lib c.id "mul" (polyValue prod.toArray.toList)

/-- A `divmod` fixture over `ℤ` (exact division only — Lean's integer
`divMod` and python-flint's `fmpz_poly` agree exactly when the
quotient is itself integral). -/
private structure DivModCase where
  id        : String
  dividend  : List Int
  divisor   : List Int

private def divModCases : List DivModCase := [
  { id := "divmod/exact",
    dividend := [-3, 15, 8, -10, -4],
    divisor  := [-1, 5, 2] },
  { id := "divmod/byMonic",
    dividend := [1, -2, 0, 1],
    divisor  := [-1, 1] }
]

private def emitDivModCase (c : DivModCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/dividend") c.dividend
  emitPolyFixture lib (c.id ++ "/divisor")  c.divisor
  let a : DensePoly Int := ofCoeffs c.dividend.toArray
  let b : DensePoly Int := ofCoeffs c.divisor.toArray
  let (q, r) := divMod a b
  emitResult lib c.id "divmod" (divModValue q.toArray.toList r.toArray.toList)

end Hex.PolyEmit

def main : IO Unit := do
  for c in Hex.PolyEmit.mulCases    do Hex.PolyEmit.emitMulCase    c
  for c in Hex.PolyEmit.divModCases do Hex.PolyEmit.emitDivModCase c
