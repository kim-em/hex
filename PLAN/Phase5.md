# Phase 5: Implementation Work Loop

**Coupling:** local. Library L can start Phase 5 once
`libraries.yml[L].done_through ≥ 4`. L's own proofs only rely on deps'
declared APIs (from the dep's Phase 1), not on deps' proofs.

Fill in `sorry`'d proofs. One GitHub issue per theorem or small group
of related theorems.

## Task selection

In priority order:
1. Items that unblock the most downstream work (high fan-out in the DAG).
2. Items assessed as mathematically hardest (from Phase 2 review or
   periodic status checks).
3. Items with the most `sorry`s in a single file.

## Workflow

- **Work top-down.** Replace `sorry` with structured proof skeletons
  (tactic blocks with intermediate `sorry`s) before filling in helper
  lemmas. This reveals the proof structure early.

- **Push sorries earlier.** When a proof is hard, replace it with a proof outline
  that cites new, clearly-stated lemmas (which may themselves be
  `sorry`) one level closer to the foundations. See
  `SPEC/design-principles.md` for the authoritative statement of the
  idiom.

- **PRs with auto-merge** enabled where CI is passing.

- **Periodic status checks** (every ~50 merged PRs or at natural
  milestones): regression check for definition-level sorries, identify
  hardest remaining items, flag neglected libraries.

## Exit criteria

For library `hex-foo`, Phase 5 is done when it has zero `sorry`
occurrences (counted across all declarations, not just top-level
theorems), `lake build` is green on the pinned toolchain, and the
Phase 3 conformance suite for the library still passes.

Record completion by bumping `libraries.yml[L].done_through` to `5`.
