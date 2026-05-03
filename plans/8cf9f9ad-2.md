**Current state**

`HexGramSchmidt/Int.lean` defines `scaledCoeffs : Matrix Int n m → Matrix Int n n`
via `scaledCoeffArrayLoop`, which runs a no-pivot fraction-free
Gram elimination over `gramRows b` and records each scaled
coefficient column with `writeScaledColumn` immediately before
the elimination step zeroes it. Two structural facts about the
shape of the resulting matrix are still `sorry`:

```lean
theorem scaledCoeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi))

theorem scaledCoeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0
```

These are the "the diagonal is the Gram determinant, above the
diagonal is zero" shape lemmas referenced in the file's docstring
for `scaledCoeffs`. They are needed by every later `Update.lean`
adjacent-swap update rule that reads scaled coefficients along
the diagonal or above.

**Deliverables**

1. Prove `scaledCoeffs_upper` by a loop-invariant over
   `scaledCoeffArrayLoop`: the `coeffs` field starts as
   `zeroRows n` (everything zero), and at each step
   `writeScaledColumn` only mutates entries `coeffs[k][k]` and
   `coeffs[i][k]` for `i ∈ [k+1, n)` — never any entry
   `coeffs[i][j]` with `j > i`. Conclude that for every
   `i < j < n`, `getArrayEntry (scaledCoeffRows b) i j = 0`,
   hence `GramSchmidt.entry (scaledCoeffs b) ⟨i, _⟩ ⟨j, _⟩ = 0`.
2. Prove `scaledCoeffs_diag` by the same loop invariant carried
   one step further: at the start of step `k`, the working
   `state.matrix` agrees on its `(k, k)` entry with
   `Int.ofNat (gramDet b (k + 1) _)` (the standard Bareiss
   leading-pivot identity over Gram matrices). When
   `writeScaledColumn` fires, it copies that entry into
   `coeffs[k][k]`, so `getArrayEntry (scaledCoeffRows b) i i =
   Int.ofNat (gramDet b (i + 1) _)`. Use the same Bareiss
   leading-pivot lemma the companion issue introduced for
   `gramDetVec_eq_gramDet`; if it lives in a different namespace,
   thread it through unchanged.
3. Preserve every executable definition: do not change
   `scaledCoeffs`, `scaledCoeffRows`, `scaledCoeffArrayLoop`,
   `writeScaledColumn`, `stepScaledRows`, `gramRows`,
   `zeroRows`, `setArrayEntry`, `getArrayEntry`, or
   `rowsToMatrix`. Helper lemmas about these definitions may be
   introduced privately.

**Context**

- `HexGramSchmidt/Int.lean` around `scaledCoeffArrayLoop`,
  `writeScaledColumn`, `stepScaledRows`, `scaledCoeffRows`,
  `scaledCoeffs`, and the two `sorry`s at lines 232 and 237.
- `HexMatrix/Bareiss.lean` for the no-pivot Bareiss recurrence
  used as the model for `scaledCoeffArrayLoop`.
- `SPEC/Libraries/hex-gram-schmidt.md` for the design contract
  describing the diagonal as `d_{j+1}` and entries above the
  diagonal as zero.
- `PLAN/Phase5.md` for the work-loop conventions.

If you need a Gram-matrix-specific Bareiss leading-pivot lemma
(`bareissNoPivotData (gramMatrix b)` has its `(k, k)` entry equal
to the `k+1`-th leading Gram determinant on the non-singular
prefix), introduce it as a small private helper rather than
inlining the algebra into both proofs.

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

- Do not prove `gramDet_zero`, `gramDetVec_eq_gramDet`,
  `gramDet_eq_prod_normSq`, `gramDet_pos`, `basis_normSq`,
  `scaledCoeffs_eq`, or `normSq_latticeVec_ge_min_basis_normSq` —
  these are separate work items.
- Do not modify `HexGramSchmidt/Update.lean`, top-level `PLAN.md`,
  top-level `AGENTS.md`, or any `SPEC/` file.
- Do not change executable Bareiss, Gram-matrix, or
  scaled-coefficient definitions.
