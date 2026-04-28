import Init.Grind.Ring.Field
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

/-- Natural-number literals in characteristic two reduce to their parity. -/
def natCast (k : Nat) : GF2n n irr hn hn64 hirr :=
  reduce (if k % 2 = 0 then 0 else 1)

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

instance : NatCast (GF2n n irr hn hn64 hirr) where
  natCast := natCast

instance (k : Nat) : OfNat (GF2n n irr hn hn64 hirr) k where
  ofNat := natCast k

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

/-- Natural scalar multiplication in characteristic two depends only on the
parity of the scalar. -/
def nsmul (k : Nat) (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if k % 2 = 0 then 0 else a

instance : SMul Nat (GF2n n irr hn hn64 hirr) where
  smul := nsmul

/-- Multiplication uses the carry-less word primitive followed by reduction
modulo the packed irreducible. -/
def mul (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  let (hi, lo) := clmul a.val b.val
  reduceWide hi lo

instance : Mul (GF2n n irr hn hn64 hirr) where
  mul := mul

/-- Natural power in `GF(2^n)` by repeated squaring. -/
def pow (a : GF2n n irr hn hn64 hirr) (k : Nat) : GF2n n irr hn hn64 hirr :=
  let rec go (acc base : GF2n n irr hn hn64 hirr) (k : Nat) : GF2n n irr hn hn64 hirr :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then acc * base else acc
      let base' := base * base
      go acc' base' (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go 1 a k

instance : Pow (GF2n n irr hn hn64 hirr) Nat where
  pow := pow

/-- Integer literals also reduce to parity because `-1 = 1` in characteristic
two. -/
def intCast (k : Int) : GF2n n irr hn hn64 hirr :=
  natCast k.natAbs

instance : IntCast (GF2n n irr hn hn64 hirr) where
  intCast := intCast

/-- Integer scalar multiplication depends only on parity as well. -/
def zsmul (k : Int) (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if k.natAbs % 2 = 0 then 0 else a

instance : SMul Int (GF2n n irr hn hn64 hirr) where
  smul := zsmul

/-- The extended Euclidean witness supplies an inverse candidate modulo the
packed irreducible. -/
private def invWord (w : UInt64) : UInt64 :=
  reducePoly (n := n) (irr := irr)
    ((GF2Poly.xgcd (toPolyWord w) (modulus (n := n) (irr := irr))).left)

/-- Inversion follows the packed extended-GCD path and uses the usual junk
value `0⁻¹ = 0`. -/
def inv (a : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  if a.val == 0 then
    0
  else
    ⟨invWord (n := n) (irr := irr) a.val, by
      sorry⟩

instance : Inv (GF2n n irr hn hn64 hirr) where
  inv := inv

/-- Division is multiplication by the inverse candidate. -/
def div (a b : GF2n n irr hn hn64 hirr) : GF2n n irr hn hn64 hirr :=
  a * b⁻¹

instance : Div (GF2n n irr hn hn64 hirr) where
  div := div

/-- Integer exponentiation uses inversion for negative exponents. -/
def zpow (a : GF2n n irr hn hn64 hirr) : Int → GF2n n irr hn hn64 hirr
  | .ofNat k => a ^ k
  | .negSucc k => (a ^ (k + 1))⁻¹

instance : HPow (GF2n n irr hn hn64 hirr) Int (GF2n n irr hn hn64 hirr) where
  hPow := zpow

theorem div_eq_mul_inv (a b : GF2n n irr hn hn64 hirr) :
    a / b = a * b⁻¹ :=
  rfl

@[simp] theorem inv_zero : (0 : GF2n n irr hn hn64 hirr)⁻¹ = 0 := by
  sorry

theorem mul_inv_cancel (a : GF2n n irr hn hn64 hirr) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  sorry

instance : Lean.Grind.Semiring (GF2n n irr hn hn64 hirr) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    sorry
  · intro a b
    sorry
  · intro a b c
    sorry
  · intro a b c
    sorry
  · intro a
    sorry
  · intro a
    sorry
  · intro a b c
    sorry
  · intro a b c
    sorry
  · intro a
    sorry
  · intro a
    sorry
  · intro a
    sorry
  · intro a m
    sorry
  · intro m
    sorry
  · intro m
    sorry
  · intro m a
    sorry

instance : Lean.Grind.Ring (GF2n n irr hn hn64 hirr) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    sorry
  · intro a b
    sorry
  · intro i a
    sorry
  · intro m a
    sorry
  · intro m
    sorry
  · intro i
    sorry

instance : Lean.Grind.CommRing (GF2n n irr hn hn64 hirr) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  sorry

instance : Lean.Grind.Field (GF2n n irr hn hn64 hirr) := by
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    sorry
  · intro h
    sorry
  · sorry
  · intro a ha
    sorry
  · intro a
    sorry
  · intro a m
    sorry
  · intro a m
    sorry

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

/-- Natural-number literals reduce to parity in characteristic two. -/
def natCast (k : Nat) : GF2nPoly f hirr :=
  reducePoly (if k % 2 = 0 then 0 else 1)

instance : NatCast (GF2nPoly f hirr) where
  natCast := natCast

instance (k : Nat) : OfNat (GF2nPoly f hirr) k where
  ofNat := natCast k

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

/-- Natural scalar multiplication depends only on parity. -/
def nsmul (k : Nat) (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if k % 2 = 0 then 0 else a

instance : SMul Nat (GF2nPoly f hirr) where
  smul := nsmul

/-- Multiplication uses packed `GF2Poly` multiplication followed by reduction
modulo the irreducible defining polynomial. -/
def mul (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  reducePoly (a.val * b.val)

instance : Mul (GF2nPoly f hirr) where
  mul := mul

/-- Natural power in the packed quotient field by repeated squaring. -/
def pow (a : GF2nPoly f hirr) (k : Nat) : GF2nPoly f hirr :=
  let rec go (acc base : GF2nPoly f hirr) (k : Nat) : GF2nPoly f hirr :=
    if hk : k = 0 then
      acc
    else
      let acc' := if k % 2 = 1 then acc * base else acc
      let base' := base * base
      go acc' base' (k / 2)
  termination_by k
  decreasing_by
    simp_wf
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by decide)
  go 1 a k

instance : Pow (GF2nPoly f hirr) Nat where
  pow := pow

/-- Integer literals reduce to parity. -/
def intCast (k : Int) : GF2nPoly f hirr :=
  natCast k.natAbs

instance : IntCast (GF2nPoly f hirr) where
  intCast := intCast

/-- Integer scalar multiplication depends only on parity. -/
def zsmul (k : Int) (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if k.natAbs % 2 = 0 then 0 else a

instance : SMul Int (GF2nPoly f hirr) where
  smul := zsmul

/-- The extended Euclidean witness supplies an inverse candidate modulo the
packed irreducible. -/
private def invPoly (p : GF2Poly) : GF2Poly :=
  (GF2Poly.xgcd p (modulus (f := f))).left

/-- Inversion follows the packed extended-GCD path and uses the usual junk
value `0⁻¹ = 0`. -/
def inv (a : GF2nPoly f hirr) : GF2nPoly f hirr :=
  if a.val.isZero then
    0
  else
    reducePoly (invPoly (f := f) a.val)

instance : Inv (GF2nPoly f hirr) where
  inv := inv

/-- Division is multiplication by the inverse candidate. -/
def div (a b : GF2nPoly f hirr) : GF2nPoly f hirr :=
  a * b⁻¹

instance : Div (GF2nPoly f hirr) where
  div := div

/-- Integer exponentiation uses inversion for negative exponents. -/
def zpow (a : GF2nPoly f hirr) : Int → GF2nPoly f hirr
  | .ofNat k => a ^ k
  | .negSucc k => (a ^ (k + 1))⁻¹

instance : HPow (GF2nPoly f hirr) Int (GF2nPoly f hirr) where
  hPow := zpow

theorem div_eq_mul_inv (a b : GF2nPoly f hirr) :
    a / b = a * b⁻¹ :=
  rfl

@[simp] theorem inv_zero : (0 : GF2nPoly f hirr)⁻¹ = 0 := by
  sorry

theorem mul_inv_cancel (a : GF2nPoly f hirr) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  sorry

instance : Lean.Grind.Semiring (GF2nPoly f hirr) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    sorry
  · intro a b
    sorry
  · intro a b c
    sorry
  · intro a b c
    sorry
  · intro a
    sorry
  · intro a
    sorry
  · intro a b c
    sorry
  · intro a b c
    sorry
  · intro a
    sorry
  · intro a
    sorry
  · intro a
    sorry
  · intro a m
    sorry
  · intro m
    sorry
  · intro m
    sorry
  · intro m a
    sorry

instance : Lean.Grind.Ring (GF2nPoly f hirr) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro a
    sorry
  · intro a b
    sorry
  · intro i a
    sorry
  · intro m a
    sorry
  · intro m
    sorry
  · intro i
    sorry

instance : Lean.Grind.CommRing (GF2nPoly f hirr) := by
  refine Lean.Grind.CommRing.mk ?_
  intro a b
  sorry

instance : Lean.Grind.Field (GF2nPoly f hirr) := by
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    sorry
  · intro h
    sorry
  · sorry
  · intro a ha
    sorry
  · intro a
    sorry
  · intro a m
    sorry
  · intro a m
    sorry

end GF2nPoly
end Hex
