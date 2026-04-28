import HexArith.Nat.ModArith
import HexArith.Barrett.ReduceNat
import HexArith.Barrett.Reduce
import HexArith.Barrett.Context
import HexArith.ExtGcd
import HexArith.Montgomery.Context
import HexArith.Montgomery.InvNat
import HexArith.Montgomery.Redc
import HexArith.Montgomery.RedcNat
import HexArith.UInt64.Wide

/-!
`HexArith` collects the low-level arithmetic substrate for the project:
wide-word `UInt64` operations, Nat-level modular-arithmetic lemmas, the
extended-GCD scaffold, and later modular reduction and number-theory layers
built on top of them.
-/
