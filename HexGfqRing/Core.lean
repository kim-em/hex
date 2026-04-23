import HexPolyFp

/-!
Core quotient-representation scaffolding for `HexGfqRing`.

This module introduces the canonical-remainder boundary for quotient
rings of `FpPoly p` modulo a nonconstant polynomial `f`. It provides the
executable `reduceMod` wrapper, the `PolyQuotient` carrier storing a
canonical representative, and the first theorem surface around `ofPoly`
and `repr` needed by downstream ring and field layers.
-/

namespace HexGfqRing

open HexPolyFp

variable {p : Nat} [NeZero p]

/--
Canonical remainder representative modulo `f`.

The executable implementation currently routes through the shared monic
remainder shell from `HexPolyFp`; later phases establish the intended
quotient semantics and sharpen the hypotheses under which this is the
canonical representative.
-/
def reduceMod (f : FpPoly p) (a : FpPoly p) : FpPoly p :=
  FpPoly.modMonic a f

/--
Elements of `F_p[x] / (f)` represented by a reduced polynomial modulo
the fixed nonconstant modulus `f`.
-/
structure PolyQuotient (p : Nat) [NeZero p] (f : FpPoly p) (hf : 0 < f.degree) where
  /-- Stored polynomial representative. -/
  repr : FpPoly p
  /-- The stored representative is already reduced modulo `f`. -/
  canonical : reduceMod f repr = repr

namespace PolyQuotient

variable {f : FpPoly p} {hf : 0 < f.degree}

/-- Build a quotient element by reducing an arbitrary polynomial modulo `f`. -/
def ofPoly (a : FpPoly p) : PolyQuotient p f hf where
  repr := reduceMod f a
  canonical := by
    sorry

/-- Read the stored canonical representative. -/
def reprPoly (x : PolyQuotient p f hf) : FpPoly p :=
  x.repr

/-- `ofPoly` stores the reduced representative by definition. -/
theorem repr_ofPoly (a : FpPoly p) :
    (ofPoly (f := f) (hf := hf) a).repr = reduceMod f a := by
  rfl

/-- The stored representative of a quotient element is reduced modulo `f`. -/
theorem reduceMod_repr (x : PolyQuotient p f hf) :
    reduceMod f x.repr = x.repr := by
  exact x.canonical

/--
Reducing a polynomial before applying `ofPoly` does not change the
resulting quotient element.
-/
theorem ofPoly_reduceMod (a : FpPoly p) :
    ofPoly (f := f) (hf := hf) (reduceMod f a) = ofPoly (f := f) (hf := hf) a := by
  sorry

/--
For nonzero monic moduli, canonical representatives are zero or have
degree strictly below `f`.
-/
theorem repr_degree_lt (x : PolyQuotient p f hf)
    (hmonic : HexPoly.DensePoly.Monic f) (hneq : f ≠ 0) :
    x.repr.natDegree? = none ∨ x.repr.degree < f.degree := by
  sorry

/--
The representative produced by `ofPoly` is zero or has degree strictly
below a nonzero monic modulus.
-/
theorem repr_ofPoly_degree_lt (a : FpPoly p)
    (hmonic : HexPoly.DensePoly.Monic f) (hneq : f ≠ 0) :
    (ofPoly (f := f) (hf := hf) a).repr.natDegree? = none ∨
      (ofPoly (f := f) (hf := hf) a).repr.degree < f.degree := by
  simpa [repr_ofPoly] using repr_degree_lt (f := f) (hf := hf)
    (x := ofPoly (f := f) (hf := hf) a) hmonic hneq

end PolyQuotient

/-- Smart constructor reducing an `FpPoly` into the quotient carrier. -/
def ofPoly {f : FpPoly p} (hf : 0 < f.degree) (a : FpPoly p) : PolyQuotient p f hf :=
  PolyQuotient.ofPoly (f := f) (hf := hf) a

/-- Projection to the stored canonical representative. -/
def repr {f : FpPoly p} {hf : 0 < f.degree} (x : PolyQuotient p f hf) : FpPoly p :=
  x.repr

/-- The top-level projection agrees with the structure field. -/
theorem repr_ofPoly {f : FpPoly p} {hf : 0 < f.degree} (a : FpPoly p) :
    repr (ofPoly (f := f) hf a) = reduceMod f a := by
  rfl

/-- Top-level `repr` preserves the reduced-representative invariant. -/
theorem reduceMod_repr {f : FpPoly p} {hf : 0 < f.degree} (x : PolyQuotient p f hf) :
    reduceMod f (repr x) = repr x := by
  exact x.canonical

end HexGfqRing
