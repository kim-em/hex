import HexConway.Basic

/-!
Core conformance checks for the Tier 1 committed Conway-polynomial lookup
surface in `HexConway`.

Oracle: cypari2 + Lübeck flat-file cache (`scripts/oracle/conway_pari.py`)
Mode: always
Covered operations:
- `luebeckConwayPolynomial?`
- `SupportedEntry`
- `conwayPoly`
Covered properties:
- the committed `(2, 1)` lookup agrees exactly with `supportedEntry_2_1`
- `conwayPoly` returns the polynomial packaged by its `SupportedEntry`
- the supported Conway polynomial has positive degree
- across `p ∈ {2, 3, 5, 7, 11, 13}, n ∈ {1, ..., 6}` the lookup either
  hits the committed `(2, 1)` entry or returns `none` (the oracle then
  cross-checks the Lübeck cache against PARI on every fixture and
  against Lean wherever Lean has committed an entry)
Covered edge cases:
- the committed binary linear hit `(2, 1)`
- unsupported binary degrees `0`, `2`, ..., `6`
- unsupported odd-prime lookups across the full oracle coverage range
-/

namespace Hex
namespace Conway
namespace ConwayConformance

private instance boundsThree    : ZMod64.Bounds 3  := ⟨by decide, by decide⟩
private instance boundsFive     : ZMod64.Bounds 5  := ⟨by decide, by decide⟩
private instance boundsSeven    : ZMod64.Bounds 7  := ⟨by decide, by decide⟩
private instance boundsEleven   : ZMod64.Bounds 11 := ⟨by decide, by decide⟩
private instance boundsThirteen : ZMod64.Bounds 13 := ⟨by decide, by decide⟩

private def coeffNats {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

#guard luebeckConwayPolynomial? 2 1 = some luebeckConwayPolynomial_2_1
#guard luebeckConwayPolynomial? 2 0 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 2 2 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 2 3 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 3 1 = (none : Option (FpPoly 3))
#guard luebeckConwayPolynomial? 5 2 = (none : Option (FpPoly 5))

#guard coeffNats luebeckConwayPolynomial_2_1 = [1, 1]
#guard supportedEntry_2_1.poly = luebeckConwayPolynomial_2_1
#guard luebeckConwayPolynomial? 2 1 = some supportedEntry_2_1.poly

#guard conwayPoly 2 1 supportedEntry_2_1 = luebeckConwayPolynomial_2_1
#guard luebeckConwayPolynomial? 2 1 =
  some (conwayPoly 2 1 supportedEntry_2_1)
#guard 0 < FpPoly.degree (conwayPoly 2 1 supportedEntry_2_1)

/-! Lookup behaviour across the full oracle coverage range
`p ∈ {2, 3, 5, 7, 11, 13}, n ∈ {1, ..., 6}` (mirrors
`HexConway/EmitFixtures.lean` and `scripts/oracle/conway_lubeck.json`).
The `(2, 1)` row hits the committed entry; every other row exercises
the `none` branch. -/

#guard luebeckConwayPolynomial? 2 1 = some luebeckConwayPolynomial_2_1
#guard luebeckConwayPolynomial? 2 2 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 2 3 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 2 4 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 2 5 = (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 2 6 = (none : Option (FpPoly 2))

#guard luebeckConwayPolynomial? 3 1 = (none : Option (FpPoly 3))
#guard luebeckConwayPolynomial? 3 2 = (none : Option (FpPoly 3))
#guard luebeckConwayPolynomial? 3 3 = (none : Option (FpPoly 3))
#guard luebeckConwayPolynomial? 3 4 = (none : Option (FpPoly 3))
#guard luebeckConwayPolynomial? 3 5 = (none : Option (FpPoly 3))
#guard luebeckConwayPolynomial? 3 6 = (none : Option (FpPoly 3))

#guard luebeckConwayPolynomial? 5 1 = (none : Option (FpPoly 5))
#guard luebeckConwayPolynomial? 5 2 = (none : Option (FpPoly 5))
#guard luebeckConwayPolynomial? 5 3 = (none : Option (FpPoly 5))
#guard luebeckConwayPolynomial? 5 4 = (none : Option (FpPoly 5))
#guard luebeckConwayPolynomial? 5 5 = (none : Option (FpPoly 5))
#guard luebeckConwayPolynomial? 5 6 = (none : Option (FpPoly 5))

#guard luebeckConwayPolynomial? 7 1 = (none : Option (FpPoly 7))
#guard luebeckConwayPolynomial? 7 2 = (none : Option (FpPoly 7))
#guard luebeckConwayPolynomial? 7 3 = (none : Option (FpPoly 7))
#guard luebeckConwayPolynomial? 7 4 = (none : Option (FpPoly 7))
#guard luebeckConwayPolynomial? 7 5 = (none : Option (FpPoly 7))
#guard luebeckConwayPolynomial? 7 6 = (none : Option (FpPoly 7))

#guard luebeckConwayPolynomial? 11 1 = (none : Option (FpPoly 11))
#guard luebeckConwayPolynomial? 11 2 = (none : Option (FpPoly 11))
#guard luebeckConwayPolynomial? 11 3 = (none : Option (FpPoly 11))
#guard luebeckConwayPolynomial? 11 4 = (none : Option (FpPoly 11))
#guard luebeckConwayPolynomial? 11 5 = (none : Option (FpPoly 11))
#guard luebeckConwayPolynomial? 11 6 = (none : Option (FpPoly 11))

#guard luebeckConwayPolynomial? 13 1 = (none : Option (FpPoly 13))
#guard luebeckConwayPolynomial? 13 2 = (none : Option (FpPoly 13))
#guard luebeckConwayPolynomial? 13 3 = (none : Option (FpPoly 13))
#guard luebeckConwayPolynomial? 13 4 = (none : Option (FpPoly 13))
#guard luebeckConwayPolynomial? 13 5 = (none : Option (FpPoly 13))
#guard luebeckConwayPolynomial? 13 6 = (none : Option (FpPoly 13))

end ConwayConformance
end Conway
end Hex
