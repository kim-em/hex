**Current state**

`HexGramSchmidt/Int.lean` defines `gramDet b k hk` (the `k`-th leading
principal Gram determinant via the row-pivoted Bareiss recurrence,
exposed as a `Nat`) and `gramDetVec b` (the full vector of leading
Gram determinants computed in one no-pivot Bareiss pass via
`gramDetVecEntry`). Two foundational equalities relating these
definitions to each other and to the empty case are still `sorry`:

```lean
theorem gramDet_zero (b : Matrix Int n m) :
    gramDet b 0 (Nat.zero_le n) = 1

theorem gramDetVec_eq_gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    (gramDetVec b).get ⟨k, Nat.lt_succ_of_le hk⟩ = gramDet b k hk
```

Downstream `Int.lean` lemmas (`gramDet_eq_prod_normSq`, `gramDet_pos`,
`scaledCoeffs_eq`, `scaledCoeffs_diag`) and `Update.lean`
adjacent-swap update lemmas all assume these facts when relating the
vector packaging to per-column results. Closing them unblocks the
rest of the Gram-determinant infrastructure.

**Deliverables**

1. Prove `gramDet_zero`: the Bareiss determinant of the empty
   `0 × 0` leading Gram matrix is `1`. The `gramDet` body unfolds
   to `(Matrix.bareiss (leadingGramMatrixInt b 0 _)).toNat`; on
   `n = 0` the row-pivoted Bareiss state never enters
   `pivotArrayLoop`'s body, leaves `singularStep = none` and
   `rowSwaps = 0`, and `arrayLastDiag? _ 0 = none`, so
   `bareissArrayDet` returns `arraySign 0 = 1`. Cast to `Nat` and
   conclude `1 = 1`.
2. Prove `gramDetVec_eq_gramDet`: both sides compute the `k`-th
   leading Gram determinant of `Matrix.gramMatrix b`. The vector
   side runs `Matrix.bareissNoPivotData` once over the full
   `n × n` Gram matrix and reads the `r`-th diagonal (for
   `k = r + 1`), or returns `1` for `k = 0`; the function side
   runs the row-pivoted Bareiss recurrence on the `k × k` leading
   principal submatrix. Use the no-pivot Bareiss invariant on Gram
   matrices (singular leading prefix ⇒ all larger leading prefixes
   singular) and the existing leading-principal Bareiss agreement
   to identify the two values. Prove the `k = 0` and `k = r + 1`
   cases separately, mirroring `gramDetVecEntry`'s match on
   `k.val`.
3. Preserve every executable definition: do not change `gramDet`,
   `gramDetVec`, `gramDetVecEntry`, `bareissNoPivotData`,
   `leadingGramMatrixInt`, or any helper they call.

**Context**

- `HexGramSchmidt/Int.lean` around `gramDet`, `gramDetVec`,
  `gramDetVecEntry`, `bareissDiagNat`, and the two `sorry`s at
  lines 200 and 204.
- `HexMatrix/Bareiss.lean` for `bareiss`, `bareissArrayState`,
  `bareissArrayDet`, `bareissNoPivotData`, and `noPivotLoop` —
  the underlying recurrences these proofs decode.
- `SPEC/Libraries/hex-gram-schmidt.md` for the design contract on
  `gramDet` / `gramDetVec`.
- `PLAN/Phase5.md` for the work-loop conventions.

If `gramDetVec_eq_gramDet` requires an intermediate
no-pivot-Bareiss-on-Gram-matrices invariant that does not yet
exist as a stated lemma, introduce it as a small private helper
in `HexGramSchmidt/Int.lean` (or in `HexMatrix/Bareiss.lean` if
it is purely a statement about `Matrix.bareissNoPivotData`),
prove it, and use it. Keep helper definitions `private`.

**Verification**

- `lake build HexGramSchmidt.Int`
- `lake build HexGramSchmidt`
- `python3 scripts/status.py HexGramSchmidt`
- `python3 scripts/check_dag.py`
- `git diff --check`
- Scan touched files for forbidden placeholders: no `axiom`, no
  `native_decide`, no `TODO`/`FIXME`, and no new `sorry` outside
  pre-existing proof bodies (the two `sorry`s above must
  disappear, and no new ones may appear).

**Out of scope**

- Do not prove `gramDet_eq_prod_normSq`, `gramDet_pos`,
  `basis_normSq`, `scaledCoeffs_eq`, `scaledCoeffs_diag`,
  `scaledCoeffs_upper`, `normSq_latticeVec_ge_min_basis_normSq`,
  or the `bareiss_eq_det` bridge — those are separate work
  items.
- Do not modify `HexGramSchmidt/Update.lean`,
  `HexGramSchmidt/Basic.lean`, top-level `PLAN.md`, top-level
  `AGENTS.md`, or any `SPEC/` file.
- Do not change executable Bareiss, Gram-matrix, or
  Gram-Schmidt definitions.
