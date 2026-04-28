import HexArith.Nat.ModArith
import HexArith.Montgomery.Context
import HexArith.Montgomery.InvNat
import HexArith.Montgomery.Redc
import HexArith.Montgomery.RedcNat
import HexArith.UInt64.Wide

/-!
`HexArith` collects the low-level arithmetic substrate for the project:
wide-word `UInt64` operations, Nat-level modular-arithmetic lemmas, and later
modular reduction and number-theory layers built on top of them.
-/
