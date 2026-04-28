import HexModArith.Basic
import HexModArith.Prime
import HexModArith.Ring
import HexModArith.Smoke

/-!
The `HexModArith` library provides `UInt64`-backed modular arithmetic,
starting from the reduced `ZMod64` core, its bounds typeclass, the basic
additive API, executable inversion and exponentiation helpers, the ring-facing
`Lean.Grind` surface, the prime-modulus theorem layer, and the default modular
multiplication surface.
-/
