import HexGf2.Core

/-!
Finite-extension carrier scaffolding for packed `GF(2)` arithmetic.

This module adds the Phase 1 packed-modulus constructor together with the
small- and large-degree carrier records used for `GF(2^n)` elements.
Executable reduction and irreducibility checking land in later issues.
-/

namespace HexGf2

namespace GF2Poly

/-- `true` exactly when the packed polynomial is the zero polynomial. -/
def IsZero (f : GF2Poly) : Prop :=
  f.words = #[]

/--
Build the monic polynomial `x^n + lower`, where `lower` stores the low
coefficients in the low bits of a `UInt64`.

This constructor is primarily used for the `n < 64` single-word carrier
surface; for larger `n`, bits above `63` in the lower part are necessarily
absent from the packed `UInt64` input.
-/
def ofUInt64Monic (lower : UInt64) (n : Nat) : GF2Poly :=
  let wordCount := n / 64 + 1
  let words0 : Array UInt64 := (List.replicate wordCount (0 : UInt64)).toArray
  let words1 := Array.set! words0 0 lower
  let wordIdx := n / 64
  let bit := (1 : UInt64) <<< (UInt64.ofNat (n % 64))
  let leadWord := words1[wordIdx]! ||| bit
  let words := Array.set! words1 wordIdx leadWord
  { words := words
    degree := n
    wf := by
      right
      sorry }

/--
Scaffold irreducibility predicate for packed `GF(2)` polynomials.

The full algebraic notion depends on division and gcd infrastructure that is
deliberately deferred to later `HexGf2` issues. Phase 1 records the intended
nontriviality boundary needed by carrier signatures.
-/
def Irreducible (f : GF2Poly) : Prop :=
  ¬ f.IsZero ∧ 0 < f.degree

end GF2Poly

/--
`GF(2^n)` packed into a single `UInt64`.

`irr` stores the lower `n` coefficients of a monic degree-`n` modulus; the
leading term is implicit and reintroduced by `GF2Poly.ofUInt64Monic`.
-/
structure GF2n (n : Nat) (irr : UInt64)
    (hn : 0 < n) (hn64 : n < 64)
    (hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)) where
  val : UInt64
  val_lt : val.toNat < 2 ^ n

/--
Packed `GF(2^n)` carrier for arbitrary-degree irreducible moduli.

The reduction invariant is stated now; executable modular arithmetic arrives
in later scaffolding slices.
-/
structure GF2nPoly (f : GF2Poly) (hirr : GF2Poly.Irreducible f) where
  val : GF2Poly
  val_reduced : val.IsZero ∨ val.degree < f.degree

end HexGf2
