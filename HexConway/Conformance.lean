import HexConway.Basic

/-!
Core conformance checks for the Tier 1 committed Conway-polynomial lookup
surface in `HexConway`.

Oracle: none
Mode: always
Covered operations:
- `luebeckConwayPolynomial?`
- `SupportedEntry`
- `conwayPoly`
Covered properties:
- the committed `(2, 1)` lookup agrees exactly with `supportedEntry_2_1`
- `conwayPoly` returns the polynomial packaged by its `SupportedEntry`
- the supported Conway polynomial has positive degree
Covered edge cases:
- the committed binary linear hit `(2, 1)`
- unsupported binary degrees `0`, `2`, and `3`
- unsupported odd-prime lookups
-/

namespace Hex
namespace Conway
namespace ConwayConformance

private instance boundsThree : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

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

end ConwayConformance
end Conway
end Hex
