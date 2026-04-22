# Phase 6: Proof Polishing

**Coupling:** local. Library L can start Phase 6 once
`libraries.yml[L].done_through ≥ 5`.

Bring sorry-free proofs to Mathlib quality. This is substantially more
than mechanical cleanup.

## Granularity

Every non-trivial definition or theorem needs separate treatment here.
This is not a "run a linter and clean up" pass — it requires careful
thought about API design for each declaration.

## What Mathlib quality means

- **Good API design.** Right level of generality; clean theorem
  statements that are easy to apply downstream.
- **Encapsulation via characterising lemmas.** Don't force users to
  unfold definitions; provide the lemmas that characterise each
  definition's behavior.
- **Avoiding defeq abuse.** Don't rely on definitional equality for
  things that should be stated as lemmas.
- **Appropriate automation annotations.** `@[simp]` lemmas for
  normalization, `@[grind]` for automated reasoning. Maximize what
  `simp` and `grind` can close automatically.
- **Clean imports and namespace management.** Minimal imports, proper
  `open` scoping, no namespace pollution.
- **Follow Mathlib's published local standards.** In particular:
  - contribution guide:
    <https://leanprover-community.github.io/contribute/index.html>
  - style guide:
    <https://leanprover-community.github.io/contribute/style.html>
  - naming conventions:
    <https://leanprover-community.github.io/contribute/naming.html>
  - documentation style:
    <https://leanprover-community.github.io/contribute/doc.html>

This project is not committing to upstreaming as part of the plan; the
point of these references is to set a local quality bar for bridge
libraries and proof-heavy cleanup.

## Exit criteria

For library `hex-foo`, Phase 6 is done when:

- the Mathlib linter is clean on the library;
- docstring coverage meets the rule in `SPEC/design-principles.md`
  (public declarations and non-obvious private helpers);
- the library contains no dead or unreferenced declarations;
- the library passes a performance regression check against the
  previous tagged benchmark baseline if one exists, otherwise
  against the most recent committed benchmark baseline (the
  bootstrap case before any release has been tagged);
- **the library's computational path runs natively in Lean** (no
  `native_decide`, no reliance on external oracles at runtime);
- **any irreducibility or field-construction claim exposed by the
  library is backed by Lean-checked evidence**, not by an external
  oracle (for libraries that expose such claims — `hex-berlekamp`,
  `hex-gfq-field`, `hex-conway`, `hex-berlekamp-zassenhaus`, etc.).

The last two criteria were previously stated as project-wide release
gates in `PLAN.md`'s "Release criteria" section. They belong here as
per-library Phase 6 exit criteria: if every library in a release set
passes them, the release inherits the guarantee automatically. See
[Releases.md](Releases.md) for the genuinely release-level check.

Record completion by bumping `libraries.yml[L].done_through` to `6`.
