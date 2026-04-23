import HexBerlekamp.Irreducibility
import HexBerlekamp.Splitting

/-!
`HexBerlekamp` re-exports the current Phase 1 factorization scaffold:
the executable Berlekamp-matrix surface for Frobenius action modulo a
polynomial, the immediate `Q_f - I` / kernel boundary, and the rank-based
irreducibility test interface together with the first `gcd(f, h - c)`
factor-splitting shell used by later factorization work.
-/

namespace HexBerlekamp
