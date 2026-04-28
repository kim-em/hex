import HexHensel.Basic
import HexHensel.Linear

/-!
The `HexHensel` library provides the executable bridge and single-step lifting
layers shared by later Hensel algorithms, starting with conversions between
`ZPoly` and `FpPoly p`, coefficientwise reduction modulo powers of `p`, and the
linear step from modulus `p^k` to `p^(k+1)`.
-/
