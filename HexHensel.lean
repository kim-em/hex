import HexHensel.Bridge
import HexHensel.Lift
import HexHensel.Linear
import HexHensel.Multifactor

/-!
`HexHensel` re-exports the executable bridge surface between integer
polynomials and residue-field polynomials together with the first
linear, iterative, and multifactor lifting scaffolds that later Hensel
algorithms build on, including the public `henselLift` wrapper.
-/

namespace HexHensel
