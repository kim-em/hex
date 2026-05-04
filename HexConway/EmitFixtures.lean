import Hex.Conformance.Emit
import HexConway

/-!
JSONL emit driver for the `hex-conway` oracle.

`lake exe hexconway_emit_fixtures` writes one JSONL record per
`(p, n)` pair in the cached Lübeck Conway-polynomial coverage range:
a `prime` fixture carrying `(p, n)` followed by a `result` record
carrying Lean's `luebeckConwayPolynomial? p n` answer.  The companion
oracle driver `scripts/oracle/conway_pari.py` reads the same stream,
queries PARI's `ffinit(p, n)` (which returns the Conway polynomial
when the entry is in PARI's database), reads the committed Lübeck
flat-file cache at `scripts/oracle/conway_lubeck.json`, and asserts
all three sources agree on the polynomial wherever Lean has committed
an entry — and that PARI ≡ Lübeck always.

Coverage matches `scripts/oracle/conway_lubeck_cache.py`:
`p ∈ {2, 3, 5, 7, 11, 13}, n ∈ {1, ..., 6}` (36 entries).  Lean's
committed table currently only includes `(2, 1)`; the other entries
emit `result.value = null` so the oracle still cross-checks PARI vs.
the Lübeck cache for them.
-/

namespace Hex.ConwayEmit

open Hex.Conformance.Emit
open Hex.Conway

private def lib : String := "HexConway"

private instance boundsTwo    : ZMod64.Bounds 2  := ⟨by decide, by decide⟩
private instance boundsThree  : ZMod64.Bounds 3  := ⟨by decide, by decide⟩
private instance boundsFive   : ZMod64.Bounds 5  := ⟨by decide, by decide⟩
private instance boundsSeven  : ZMod64.Bounds 7  := ⟨by decide, by decide⟩
private instance boundsEleven : ZMod64.Bounds 11 := ⟨by decide, by decide⟩
private instance boundsThirteen : ZMod64.Bounds 13 := ⟨by decide, by decide⟩

/-- Render an `Option (List Nat)` as either `null` or a JSON list of
ints (Conway-polynomial coefficients are always nonnegative). -/
private def optPolyValue : Option (List Nat) → String
  | none      => "null"
  | some xs   => polyValue (xs.map Int.ofNat)

private def caseId (p n : Nat) : String :=
  s!"lookup/p{p}_n{n}"

/-- Emit a `(p, n)` fixture and a result recording Lean's committed
Conway lookup. -/
private def emitLookup (p n : Nat) [ZMod64.Bounds p] : IO Unit := do
  let id := caseId p n
  emitPrimeFixture lib (id ++ "/pn") (Int.ofNat p) (Int.ofNat n)
  let lookup : Option (FpPoly p) := luebeckConwayPolynomial? p n
  let coeffsOpt : Option (List Nat) :=
    lookup.map (fun f => f.toArray.toList.map ZMod64.toNat)
  emitResult lib id "conway_lookup" (optPolyValue coeffsOpt)

end Hex.ConwayEmit

open Hex.ConwayEmit in
def main : IO Unit := do
  -- Coverage: `p ∈ {2, 3, 5, 7, 11, 13}, n ∈ {1, ..., 6}`.  Each line
  -- emits one fixture + one result.  Keep these `(p, n)` pairs in lock
  -- step with `scripts/oracle/conway_lubeck.json`.
  for n in [1, 2, 3, 4, 5, 6] do emitLookup 2  n
  for n in [1, 2, 3, 4, 5, 6] do emitLookup 3  n
  for n in [1, 2, 3, 4, 5, 6] do emitLookup 5  n
  for n in [1, 2, 3, 4, 5, 6] do emitLookup 7  n
  for n in [1, 2, 3, 4, 5, 6] do emitLookup 11 n
  for n in [1, 2, 3, 4, 5, 6] do emitLookup 13 n
