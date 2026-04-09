# hex-poly-z (polynomials over Z, depends on hex-poly)

Specialized polynomial arithmetic over `Z`.

**Contents:**
- `ZPoly` = `DensePoly Int`
- Polynomial congruence:
  ```lean
  def ZPoly.congr (f g : ZPoly) (m : Nat) : Prop :=
      ∀ i, (f.coeff i - g.coeff i) % m = 0

  def ZPoly.coprimeModP (f g : ZPoly) (p : Nat) : Prop := ...
  ```
- Content and primitive part: `f = content(f) * primitivePart(f)`
- Mignotte bound computation: `|gⱼ| ≤ C(k,j) · ‖f‖₂` for any degree-k
  factor `g | f` in `Z[x]`. The computation is just binomial coefficients
  and the 2-norm of `f`'s coefficients. The proof that the bound is valid
  lives in `hex-poly-z-mathlib`.
**Key properties:**
- `primitivePart(f)` is primitive (content = 1)
- Gauss's lemma (`content(f * g) = content(f) * content(g)`) is not
  needed in this library — it transfers from Mathlib via the ring
  equivalence in hex-poly-z-mathlib.
