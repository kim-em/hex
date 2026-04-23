import HexLLL.Core
import HexLLL.State
import HexLLL.SizeReduce

/-!
Core LLL scaffolding.

This root module re-exports the current `HexLLL` scaffold: the
predicate surface for integer-lattice membership and leading
Gram-determinant independence, together with the integer `LLLState`
record, its proof-facing Gram-Schmidt coefficient recovery helper, and
the executable potential and size-reduction transition used by later
reduction-loop work.
-/

namespace HexLLL
