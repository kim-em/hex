import HexHensel.Basic

/-!
Executable data records for the Berlekamp-Zassenhaus factorization pipeline.

This module contains the shared records passed between prime selection,
Hensel lifting, and integer recombination in the `ZPoly` factorization
pipeline.
-/
namespace Hex

/--
Data produced by modular prime selection: the selected prime, the image of the
input polynomial over that prime field, and its modular factors.
-/
structure PrimeChoiceData where
  p : Nat
  [bounds : ZMod64.Bounds p]
  fModP : FpPoly p
  factorsModP : Array (FpPoly p)

/--
Data produced by Hensel lifting and consumed by integer recombination: the
prime, the requested lift precision, and the lifted integer factors.
-/
structure LiftData where
  p : Nat
  k : Nat
  liftedFactors : Array ZPoly

end Hex
