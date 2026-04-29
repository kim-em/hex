import HexGfqField.Basic
import HexGfqField.Operations
import HexGfqField.Conformance

/-!
Thin finite-field wrapper for executable `F_p[x] / (f)`.

`HexGfqField` reuses the quotient-ring representation from `HexGfqRing`
unchanged: `GFqField.FiniteField` is just a wrapper around reduced residues,
with explicit conversions, quotient-backed arithmetic, exponentiation, and the
Frobenius map `a ↦ a ^ p`.
-/
