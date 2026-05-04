## Current state

`conformance (HexGfqMathlib)` fails on `main` (e.g. run 25301259795 against
sha 0355ce1; same failure on every later main commit). The breakage was
exposed by PR #2024 (df1e8ee, "ci: derive conformance matrix from
Conformance.lean files"), which made the conformance matrix auto-discover
jobs from `Hex*/Conformance.lean`. `HexGfqMathlib/Conformance.lean` already
exists, so the matrix now schedules a `HexGfqMathlib` job — and the
underlying `HexGfqMathlib/Basic.lean` does not elaborate.

Symptom (from the `HexGfqMathlib/Basic.lean:78-91` errors in run
25301259795): instances `Lean.Grind.{Semiring, Ring, CommSemiring, Field}`
on `Hex.GFqField.FiniteField f hf hp hirr` cannot be synthesized inside the
`Field.ofMinimalAxioms` proof obligations. Root cause: those Grind instances
in `HexGfqField/Operations.lean:17` require
`[Hex.ZMod64.PrimeModulus p]` (PR #1849, "fix: require prime modulus for Fp
division laws") in addition to `[Hex.ZMod64.Bounds p]`, but
`HexGfqMathlib/Basic.lean:66, :152` only carries the `Bounds` instance.
`HexGfqMathlib/Conformance.lean:37` similarly only installs
`conformanceBoundsTwo`.

Knock-on effect: every PR currently shows `conformance (HexGfqMathlib)
✗FAILURE`. The PR repair flow has already closed at least two doc-only PRs
as "unsalvageable" on this basis (#2025 → human-oversight directive #2021,
#2034 → human-oversight directive #2005). Two in-flight cross-check PRs
(#2031 HexGF2 extern clmul, #2032 HexHensel linear-vs-quadratic) currently
piggyback the same fix in the same files, but that conflates unrelated
work and violates the project's "PR Scope" rule.

## Deliverables

A focused, single-purpose PR that adds the missing `PrimeModulus`
instance argument so `HexGfqMathlib/Basic.lean` and
`HexGfqMathlib/Conformance.lean` elaborate. Three small edits:

1. `HexGfqMathlib/Basic.lean:66` (in `namespace FiniteField`) — change
   ```
   variable {p : Nat} [Hex.ZMod64.Bounds p]
   ```
   to
   ```
   variable {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
   ```
2. `HexGfqMathlib/Basic.lean:152` (in `namespace GFq`) — same edit.
3. `HexGfqMathlib/Conformance.lean:37-40` — add a `private instance` for
   `Hex.ZMod64.PrimeModulus 2`, derived from the existing committed
   `Conway.SupportedEntry 2 1` prime witness:
   ```lean
   private instance conformancePrimeModulusTwo : Hex.ZMod64.PrimeModulus 2 :=
     Hex.ZMod64.primeModulusOfPrime Entry21.prime
   ```
   Insert immediately after `conformanceBoundsTwo` and before `Entry21`'s
   first downstream use (or place it after `Entry21` if
   `Entry21.prime` requires `Entry21` in scope; either ordering works).

Do **not** make any other changes — no proof tweaks, no fixture changes,
no new conformance cases. Stay surgical.

## Context

- `HexGfqMathlib/Basic.lean:66, :152` — broken variable lines.
- `HexGfqMathlib/Conformance.lean:37-40` — instance list to extend.
- `HexGfqField/Operations.lean:17` — declaration that requires
  `[ZMod64.PrimeModulus p]`.
- `HexPolyFp/Basic.lean:59` — definition of `primeModulusOfPrime`.
- PR #1849 (16c5ca8, "fix: require prime modulus for Fp division laws")
  introduced the `PrimeModulus` instance requirement on the GFqField
  Grind hierarchy without updating HexGfqMathlib downstream.
- PR #2024 (df1e8ee) made the conformance matrix auto-discover jobs,
  exposing the latent breakage.
- Pre-existing diff to mirror (DO NOT just copy — re-derive locally):
  the same edit is already piggybacked in PRs #2031 and #2032. Once
  this focused fix lands, those PRs will need to drop their copy on
  rebase.

## Verification

- `lake build HexGfqMathlib` succeeds (currently fails on `main`).
- `lake test HexGfqMathlib` succeeds — all `#guard`s in
  `HexGfqMathlib/Conformance.lean` still pass.
- CI `conformance (HexGfqMathlib)` job goes from failing to passing
  on the PR.
- `git diff main -- HexGfqMathlib/` shows only the three edits described
  above (≈4 changed lines + ≈3 added lines for the new instance).

## Out of scope

- Filling in the four `sorry`s already present in
  `HexGfqMathlib/Basic.lean:40, 46, 52, 60` (FpPoly index
  encode/decode lemmas). Those have always been there; this issue does
  not touch them.
- Sorries in `HexGfqMathlib/Basic.lean:107` (`reducedRepEquiv.left_inv`)
  or anywhere else.
- Bumping the HexGfqMathlib conformance fixture toward profile-size
  ceilings (separate concern; not currently scoped).
- Rebasing #2031 / #2032 to drop their piggybacked copies — that is
  the repair flow's job once this PR merges.

## Critical-path note

This is a `--critical-path` issue: every doc-only or unrelated PR
against main currently inherits the `conformance (HexGfqMathlib)`
failure and risks being closed as "unsalvageable" by the repair flow.
Two unclaimed `human-oversight` directives (#2021, #2005) are stuck
behind exactly this failure mode. Land this fix first.
