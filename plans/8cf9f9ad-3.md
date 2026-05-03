**Current state**

`HexPolyZ/Basic.lean` defines `primitiveSquareFreeDecomposition`
case-by-case on `(primitivePart f).isZero` and the rational
derivative `derivative.isZero`, with the non-degenerate branch
producing `squareFreeCore := ratPolyPrimitivePart (ratPrimitive /
repeatedRat)` where `repeatedRat = DensePoly.gcd ratPrimitive
derivative`. The companion theorem
`primitiveSquareFreeDecomposition_reassembly_over_rat` is proved
in this file and pinpoints the rational unit relating the
recovered factors back to the input.

The remaining `sorry` at line 930 is the square-free core property
itself:

```lean
theorem primitiveSquareFreeDecomposition_squareFreeCore
    (f : ZPoly)
    (hcore : (primitiveSquareFreeDecomposition f).squareFreeCore ≠ 0) :
    SquareFreeRat (primitiveSquareFreeDecomposition f).squareFreeCore
```

`SquareFreeRat g := DensePoly.gcd (toRatPoly g) (DensePoly.derivative
(toRatPoly g)) = 1`. This is the last Phase 5 obligation in the
HexPolyZ rational square-free decomposition surface.

The file already has the local `ratDivModLaws` and `ratGcdLaws`
instances (private, with several fields still `sorry`), the
`rat_div_gcd_mul_reconstruct` helper, and
`ratPolyPrimitivePart_rational_associate` for moving between the
rational gcd quotient and its primitive integer representative.

**Deliverables**

1. Prove `primitiveSquareFreeDecomposition_squareFreeCore`.
   Dispatch on the same three executable branches as
   `primitiveSquareFreeDecomposition`:
   - `(primitivePart f).isZero = true`: `squareFreeCore = 0`,
     contradicts `hcore`.
   - derivative branch zero: `squareFreeCore = primitivePart f`;
     reduce `SquareFreeRat` to a fact about `toRatPoly
     (primitivePart f)` and its (zero) rational derivative. The
     hypothesis `derivative.isZero = true` makes
     `DensePoly.gcd ratPrimitive 0 = ratPrimitive` and forces
     the rational `gcd` of `ratPrimitive` with its derivative
     to be the constant `1` after primitive normalization.
   - main branch: `squareFreeCore = ratPolyPrimitivePart
     (ratPrimitive / repeatedRat)`. Reduce
     `SquareFreeRat` to a property of the rational quotient
     `ratPrimitive / repeatedRat` and its derivative, then
     transfer through `ratPolyPrimitivePart_rational_associate`
     using the rational-unit invariance of `DensePoly.gcd` and
     `DensePoly.derivative`.
2. If the main-branch reduction needs a new helper (for example
   "the rational gcd is invariant under nonzero rational scaling",
   or "the rational derivative scales by the same nonzero unit"),
   introduce it as a private lemma adjacent to the existing
   `rat_*` helpers in `HexPolyZ/Basic.lean`. Do not change the
   public API of any other file.
3. Preserve every executable definition: do not change
   `primitiveSquareFreeDecomposition`, `squareFreeCore`,
   `ratPolyPrimitivePart`, `ratPrimitive`, `derivative`,
   `repeatedRat`, `toRatPoly`, `DensePoly.gcd`,
   `DensePoly.derivative`, or any other dense-polynomial
   executable surface.

**Context**

- `HexPolyZ/Basic.lean` around lines 405–433 (the executable
  `primitiveSquareFreeDecomposition`), 877–928 (the proved
  `primitiveSquareFreeDecomposition_reassembly_over_rat`), and
  the `sorry` at line 930.
- `HexPolyZ/Basic.lean` lines 812–859 for the local
  `ratDivModLaws` / `ratGcdLaws` instances (private; some fields
  still `sorry` and may legitimately be cited by the proof).
- `HexPoly/Euclid.lean` for `DensePoly.gcd`, `DensePoly.div`,
  `DensePoly.mod`, `DensePoly.derivative`, and the
  `DivModLaws` / `GcdLaws` projections.
- `SPEC/Libraries/hex-poly-z.md` for the design contract on
  `primitiveSquareFreeDecomposition` and `SquareFreeRat`.
- `PLAN/Phase5.md` for the work-loop conventions, including the
  permission to cite other in-flight `sorry`s when the rest of
  the proof structure is sound.

If the proof needs `DensePoly.GcdLaws Rat` projections
(`gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`, `xgcd_bezout`) and
the corresponding `ratGcdLaws` field is currently `sorry`, the
proof may use the projection — Phase 5 explicitly allows
proofs that depend on still-`sorry` projections from existing
private instances, since those instances will be filled in by
companion work items. The new theorem must not introduce
*additional* `sorry`s beyond the existing private-instance
holes.

**Verification**

- `lake build HexPolyZ.Basic`
- `lake build HexPolyZ`
- `python3 scripts/status.py HexPolyZ`
- `python3 scripts/check_dag.py`
- `git diff --check`
- Scan touched files for forbidden placeholders: no `axiom`, no
  `native_decide`, no `TODO`/`FIXME`. The `sorry` at the
  `primitiveSquareFreeDecomposition_squareFreeCore` site must
  disappear; no new `sorry` may be introduced anywhere except
  the pre-existing `ratDivModLaws` / `ratGcdLaws` placeholder
  fields, which must remain unchanged.

**Out of scope**

- Do not prove the remaining `ratDivModLaws` / `ratGcdLaws`
  fields. Use the projections as a black box if needed; the
  field-side proofs are separate work items.
- Do not modify `HexPolyFp/Basic.lean`, `HexHensel/*`,
  `HexGramSchmidt/*`, `HexPoly/Operations.lean`,
  `HexPoly/Euclid.lean`, top-level `PLAN.md`, top-level
  `AGENTS.md`, or any `SPEC/` file.
- Do not change `primitiveSquareFreeDecomposition`,
  `squareFreeCore`, `ratPolyPrimitivePart`, or any executable
  polynomial definition.
