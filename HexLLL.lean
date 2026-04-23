import HexLLL.Core
import HexLLL.State
import HexLLL.SizeReduce
import HexLLL.SwapStep
import HexLLL.Loop

/-!
Core LLL scaffolding.

This root module re-exports the current `HexLLL` scaffold: the
predicate surface for integer-lattice membership and leading
Gram-determinant independence, together with the integer `LLLState`
record, its proof-facing Gram-Schmidt coefficient recovery helper, and
the executable potential, size-reduction transition, and adjacent-swap
transition, and the public loop entrypoints used by later reducedness
and correctness work.
-/

namespace HexLLL
