import HexArith.ExtGcd
import HexArith.PowMod

/-!
Deterministic core conformance fixtures for `HexArith`.

This module records replayable Lean-side fixtures for the Phase 3 core
profile, covering the `Nat`, `Int`, and `UInt64` extended-GCD entry
points together with modular exponentiation.
-/

namespace HexArith
namespace Conformance

structure FixtureMetadata where
  library : String
  profile : String
  seed : Nat
deriving Repr

structure NatExtGcdCase where
  name : String
  a : Nat
  b : Nat
  expectedGcd : Nat
  expectedS : Int
  expectedT : Int
deriving Repr

structure IntExtGcdCase where
  name : String
  a : Int
  b : Int
  expectedGcd : Nat
  expectedS : Int
  expectedT : Int
deriving Repr

structure UInt64ExtGcdCase where
  name : String
  a : Nat
  b : Nat
  expectedGcd : Nat
  expectedS : Int
  expectedT : Int
deriving Repr

structure PowModCase where
  name : String
  a : Nat
  n : Nat
  p : Nat
  expected : Nat
deriving Repr

def metadata : FixtureMetadata :=
  { library := "HexArith", profile := "core", seed := 0 }

def FixtureMetadata.serialized (m : FixtureMetadata) : String :=
  s!"library={m.library};profile={m.profile};seed={m.seed}"

def NatExtGcdCase.serialized (c : NatExtGcdCase) : String :=
  s!"kind=nat-extgcd;name={c.name};a={c.a};b={c.b};g={c.expectedGcd};s={c.expectedS};t={c.expectedT}"

def IntExtGcdCase.serialized (c : IntExtGcdCase) : String :=
  s!"kind=int-extgcd;name={c.name};a={c.a};b={c.b};g={c.expectedGcd};s={c.expectedS};t={c.expectedT}"

def UInt64ExtGcdCase.serialized (c : UInt64ExtGcdCase) : String :=
  s!"kind=uint64-extgcd;name={c.name};a={c.a};b={c.b};g={c.expectedGcd};s={c.expectedS};t={c.expectedT}"

def PowModCase.serialized (c : PowModCase) : String :=
  s!"kind=powmod;name={c.name};a={c.a};n={c.n};p={c.p};value={c.expected}"

def natExtGcd_zero_zero : NatExtGcdCase :=
  { name := "nat-zero-zero", a := 0, b := 0, expectedGcd := 0, expectedS := 1, expectedT := 0 }

def natExtGcd_zero_rhs : NatExtGcdCase :=
  { name := "nat-zero-rhs", a := 0, b := 7, expectedGcd := 7, expectedS := 0, expectedT := 1 }

def natExtGcd_composite : NatExtGcdCase :=
  { name := "nat-composite", a := 30, b := 12, expectedGcd := 6, expectedS := 1, expectedT := -2 }

def natExtGcd_cases : List NatExtGcdCase :=
  [natExtGcd_zero_zero, natExtGcd_zero_rhs, natExtGcd_composite]

def intExtGcd_pos_neg : IntExtGcdCase :=
  { name := "int-pos-neg", a := 30, b := -12, expectedGcd := 6, expectedS := 1, expectedT := 2 }

def intExtGcd_neg_pos : IntExtGcdCase :=
  { name := "int-neg-pos", a := -30, b := 12, expectedGcd := 6, expectedS := -1, expectedT := -2 }

def intExtGcd_zero_neg : IntExtGcdCase :=
  { name := "int-zero-neg", a := 0, b := -7, expectedGcd := 7, expectedS := 0, expectedT := -1 }

def intExtGcd_cases : List IntExtGcdCase :=
  [intExtGcd_pos_neg, intExtGcd_neg_pos, intExtGcd_zero_neg]

def uint64ExtGcd_zero_zero : UInt64ExtGcdCase :=
  { name := "uint64-zero-zero", a := 0, b := 0, expectedGcd := 0, expectedS := 1, expectedT := 0 }

def uint64ExtGcd_zero_rhs : UInt64ExtGcdCase :=
  { name := "uint64-zero-rhs", a := 0, b := 7, expectedGcd := 7, expectedS := 0, expectedT := 1 }

def uint64ExtGcd_composite : UInt64ExtGcdCase :=
  { name := "uint64-composite", a := 42, b := 30, expectedGcd := 6, expectedS := -2, expectedT := 3 }

def uint64ExtGcd_cases : List UInt64ExtGcdCase :=
  [uint64ExtGcd_zero_zero, uint64ExtGcd_zero_rhs, uint64ExtGcd_composite]

def powMod_zero_exp : PowModCase :=
  { name := "powmod-zero-exp", a := 7, n := 0, p := 5, expected := 1 }

def powMod_small : PowModCase :=
  { name := "powmod-small", a := 5, n := 3, p := 13, expected := 8 }

def powMod_reduce_base : PowModCase :=
  { name := "powmod-reduce-base", a := 42, n := 5, p := 17, expected := 9 }

def powMod_unit_modulus : PowModCase :=
  { name := "powmod-unit-modulus", a := 10, n := 4, p := 1, expected := 0 }

def powMod_cases : List PowModCase :=
  [powMod_zero_exp, powMod_small, powMod_reduce_base, powMod_unit_modulus]

def serializedFixtures : List String :=
  [metadata.serialized] ++
    natExtGcd_cases.map NatExtGcdCase.serialized ++
    intExtGcd_cases.map IntExtGcdCase.serialized ++
    uint64ExtGcd_cases.map UInt64ExtGcdCase.serialized ++
    powMod_cases.map PowModCase.serialized

def NatExtGcdCase.Valid (c : NatExtGcdCase) : Bool :=
  let actual := HexArith.extGcd c.a c.b
  (actual == (c.expectedGcd, c.expectedS, c.expectedT)) &&
    (actual.1 == Nat.gcd c.a c.b) &&
    (let (g, s, t) := actual
     decide (s * c.a + t * c.b = g))

def IntExtGcdCase.Valid (c : IntExtGcdCase) : Bool :=
  let actual := Hex.pureIntExtGcd c.a c.b
  (actual == (c.expectedGcd, c.expectedS, c.expectedT)) &&
    (actual.1 == Nat.gcd c.a.natAbs c.b.natAbs) &&
    (let (g, s, t) := actual
     decide (s * c.a + t * c.b = g))

theorem intExtGcd_eq_pure (a b : Int) :
    HexArith.Int.extGcd a b = Hex.pureIntExtGcd a b := by
  rfl

def UInt64ExtGcdCase.Valid (c : UInt64ExtGcdCase) : Bool :=
  let actual := HexArith.UInt64.extGcd (.ofNat c.a) (.ofNat c.b)
  (actual == (.ofNat c.expectedGcd, c.expectedS, c.expectedT)) &&
    (actual.1.toNat == Nat.gcd c.a c.b) &&
    (let (g, s, t) := actual
     decide (s * Int.ofNat c.a + t * Int.ofNat c.b = Int.ofNat g.toNat))

def PowModCase.Valid (c : PowModCase) : Bool :=
  let actual := HexArith.powMod c.a c.n c.p
  (actual == c.expected) && (actual == c.a ^ c.n % c.p)

#guard natExtGcd_zero_zero.Valid = true
#guard natExtGcd_zero_rhs.Valid = true
#guard natExtGcd_composite.Valid = true

#guard intExtGcd_pos_neg.Valid = true
#guard intExtGcd_neg_pos.Valid = true
#guard intExtGcd_zero_neg.Valid = true

#guard uint64ExtGcd_zero_zero.Valid = true
#guard uint64ExtGcd_zero_rhs.Valid = true
#guard uint64ExtGcd_composite.Valid = true

#guard powMod_zero_exp.Valid = true
#guard powMod_small.Valid = true
#guard powMod_reduce_base.Valid = true
#guard powMod_unit_modulus.Valid = true

end Conformance
end HexArith
