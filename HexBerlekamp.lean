import HexBerlekamp.Irreducibility
import HexBerlekamp.DistinctDegree
import HexBerlekamp.Rabin
import HexBerlekamp.Splitting

/-!
`HexBerlekamp` re-exports the current Phase 1 factorization scaffold:
the executable Berlekamp-matrix surface for Frobenius action modulo a
polynomial, the immediate `Q_f - I` kernel-matrix boundary, and the
rank-based irreducibility test interface together with the first
`gcd(f, h - c)` factor-splitting shell used by later factorization
work, the initial distinct-degree bucket extraction surface, and the
certificate/checker boundary for Rabin's irreducibility criterion.
-/

namespace HexBerlekamp
