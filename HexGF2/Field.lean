import HexGF2.Euclid

/-!
Single-word extension-field wrappers for `hex-gf2`.

This module adds the spec-named irreducible-modulus helper surface on top of
`GF2Poly`, then packages both the `n < 64` single-word case and the arbitrary-
degree packed-quotient case of `GF(2^n)` as reduced representatives with XOR
addition and modular multiplication modulo a fixed irreducible polynomial.
-/
namespace Hex
namespace GF2Poly

/-- Bitmask for coefficients of degree `< n` inside one `UInt64` word. -/
def lowerMask (n : Nat) : UInt64 :=
  if n < 64 then
    ((1 : UInt64) <<< n.toUInt64) - 1
  else
    (0 : UInt64) - 1

/-- Build the monic degree-`n` polynomial `x^n + lower`, truncating `lower` to
degrees `< n` as required by the packed `GF(2^n)` modulus convention. -/
def ofUInt64Monic (lower : UInt64) (n : Nat) : GF2Poly :=
  monomial n + ofUInt64 (lower &&& lowerMask n)

/-- Polynomial irreducibility over `GF(2)` phrased in terms of nontrivial
factorizations inside the packed `GF2Poly` execution model. -/
def Irreducible (f : GF2Poly) : Prop :=
  f ≠ 0 ∧ ∀ a b : GF2Poly, a * b = f → a.degree = 0 ∨ b.degree = 0

end GF2Poly

/-- `GF(2^n)` for arbitrary `n`, represented by reduced `GF2Poly` residues
modulo an irreducible polynomial. -/
structure GF2nPoly (f : GF2Poly) (hirr : GF2Poly.Irreducible f) where
  val : GF2Poly
  val_reduced : val.IsZero ∨ val.degree < f.degree

/-- `GF(2^n)` packed into one machine word. The modulus stores only the lower
`n` coefficients; the leading `x^n` term is implicit in
`GF2Poly.ofUInt64Monic irr n`. -/
structure GF2n (n : Nat) (irr : UInt64)
    (hn : 0 < n) (hn64 : n < 64)
    (hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)) where
  val : UInt64
  val_lt : val.toNat < 2 ^ n

namespace GF2n

variable {n : Nat} {irr : UInt64}
variable {hn : 0 < n} {hn64 : n < 64}
variable {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)}

/-- The packed irreducible modulus polynomial defining this extension field. -/
def modulus : GF2Poly :=
  GF2Poly.ofUInt64Monic irr n

/-- The low-word mask selecting canonical representatives of degree `< n`. -/
def mask : UInt64 :=
  GF2Poly.lowerMask n

/-- Convert a machine word into its packed polynomial representative. -/
def toPolyWord (w : UInt64) : GF2Poly :=
  GF2Poly.ofUInt64 w

/-- Convert a `UInt64 × UInt64` carry-less product into a packed polynomial. -/
def toPolyWide (hi lo : UInt64) : GF2Poly :=
  GF2Poly.ofWords #[lo, hi]

/-- Reduce a packed polynomial modulo the fixed irreducible and read back the
single-word representative. -/
def reducePoly (p : GF2Poly) : UInt64 :=
  (((p % modulus (n := n) (irr := irr)).toWords).getD 0 0) &&&
    mask (n := n)

/-- Canonical constructor from a raw word by reduction modulo the field
modulus. -/
def reduce (w : UInt64) : GF2n n irr hn hn64 hirr :=
  ⟨reducePoly (n := n) (irr := irr) (toPolyWord w), by
    sorry⟩

/-- Canonical constructor from a packed 128-bit carry-less product. -/
def reduceWide (hi lo : UInt64) : GF2n n irr hn hn64 hirr :=
  ⟨reducePoly (n := n) (irr := irr) (toPolyWide hi lo), by
    sorry⟩

/-- Canonical additive identity. -/
def zero : GF2n n irr hn hn64 hirr :=
  reduce 0

instance : Zero (GF2n n irr hn hn64 hirr) where
  zero := zero

/-- Canonical multiplicative identity. -/
def one : GF2n n irr hn hn64 hirr :=
  reduce 1

instance : One (GF2n n irr hn hn64 hirr) where
  one := one

/-- Addition in characteristic two is word-wise XOR followed by canonical
reduction. -/
def add (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  reduce (a.val ^^^ b.val)

instance : Add (GF2n n irr hn hn64 hirr) where
  add := add

/-- Negation is the identity in characteristic two. -/
def neg (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  a

instance : Neg (GF2n n irr hn hn64 hirr) where
  neg := neg

/-- Subtraction coincides with addition in characteristic two. -/
def sub (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  add a b

instance : Sub (GF2n n irr hn hn64 hirr) where
  sub := sub

/-- Multiplication uses the carry-less word primitive followed by reduction
modulo the packed irreducible. -/
def mul (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  let (hi, lo) := clmul a.val b.val
  reduceWide hi lo

instance : Mul (GF2n n irr hn hn64 hirr) where
  mul := mul

/-- Natural power in `GF(2^n)` by repeated multiplication. -/
def pow (a : GF2n n irr hn hn64 hirr) : Nat → GF2n n irr hn hn64 hirr
  | 0 => 1
  | exp + 1 => pow a exp * a

instance : Pow (GF2n n irr hn hn64 hirr) Nat where
  pow := pow

end GF2n

namespace GF2nPoly

variable {f : GF2Poly} {hirr : GF2Poly.Irreducible f}

/-- The defining irreducible modulus polynomial of the packed quotient field. -/
def modulus : GF2Poly :=
  f

/-- Reduce a packed polynomial to its canonical residue class modulo `f`. -/
def reducePoly (p : GF2Poly) : GF2nPoly f hirr :=
  ⟨p % modulus (f := f), GF2Poly.mod_degree_lt p (modulus (f := f)) hirr.1⟩

/-- Canonical additive identity. -/
def zero : GF2nPoly f hirr :=
  reducePoly 0

instance : Zero (GF2nPoly f hirr) where
  zero := zero

/-- Canonical multiplicative identity. -/
def one : GF2nPoly f hirr :=
  reducePoly 1

instance : One (GF2nPoly f hirr) where
  one := one

/-- Addition in characteristic two is XOR on representatives, followed by
canonical reduction modulo `f`. -/
def add (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  reducePoly (a.val + b.val)

instance : Add (GF2nPoly f hirr) where
  add := add

/-- Negation is the identity in characteristic two. -/
def neg (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  a

instance : Neg (GF2nPoly f hirr) where
  neg := neg

/-- Subtraction coincides with addition in characteristic two. -/
def sub (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  add a b

instance : Sub (GF2nPoly f hirr) where
  sub := sub

/-- Multiplication uses packed `GF2Poly` multiplication followed by reduction
modulo the irreducible defining polynomial. -/
def mul (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  reducePoly (a.val * b.val)

instance : Mul (GF2nPoly f hirr) where
  mul := mul

/-- Natural power in the packed quotient field by repeated multiplication. -/
def pow (a : GF2nPoly f hirr) : Nat → GF2nPoly f hirr
  | 0 => 1
  | exp + 1 => pow a exp * a

instance : Pow (GF2nPoly f hirr) Nat where
  pow := pow

end GF2nPoly
end Hex
