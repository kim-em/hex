# Phase 3: Conformance Testing

**Coupling:** dep-coupled. Library L can start Phase 3 once
`libraries.yml[L].done_through ≥ 2` and every `d ∈ L.deps` has
`libraries.yml[d].done_through ≥ 3`.

Conformance testing comes **before** proofs. No point proving theorems
about wrong implementations.

Phase 3 should follow `SPEC/testing.md`. In particular:

- Use the three testing profiles:
  - `core` — deterministic Lean-only checks with no external tools
  - `ci` — modest randomized cross-checks using external tools only when
    available
  - `local` — larger or manually triggered campaigns
- Treat failures as replayable artifacts. Record at least the library,
  profile, seed, and serialized input case.
- Keep execution-mode distinctions explicit:
  - `always`
  - `if_available`
  - `required`

## Oracle guidance

- `hex-arith`, `hex-mod-arith`: Lean built-in big integer semantics
- `hex-poly`, `hex-poly-z`, `hex-poly-fp`: FLINT or Sage polynomial
  arithmetic; `python-flint` is a useful partial oracle
- `hex-matrix`, `hex-gram-schmidt`: Sage exact matrix / rational linear
  algebra
- `hex-gf2`, `hex-gfq-ring`, `hex-gfq-field`, `hex-gfq`: Sage finite
  field and quotient-ring computations
- `hex-berlekamp`, `hex-berlekamp-zassenhaus`: FLINT or Sage
  factorization / irreducibility checks
- `hex-hensel`: Sage or FLINT Hensel lifting, plus direct congruence and
  product checks
- `hex-lll`: fpLLL or Sage `LLL`, comparing reducedness and lattice
  equality rather than exact basis equality
- `hex-conway`: committed fixtures cross-checked against Sage's Conway
  tables

## Infrastructure guidance

- Prefer JSON or JSONL for serialized test cases and normalized oracle
  outputs.
- Lean produces and consumes the shared case format; Python or shell
  drivers handle tool detection and oracle invocation.
- Sage should not rely on Ubuntu `apt` packages in CI. Prefer a
  Nix-based Sage path (`nix shell nixpkgs#sage ...`) for local and CI
  parity. `cachix/install-nix-action` is the expected GitHub Actions
  installation path when Sage-backed CI jobs are added.
- Keep standard CI small enough for hosted runners and partial tool
  availability; reserve larger runs for `local` or manual jobs.

## Exit criteria

Phase 3 is done for a library when, for each of the `core`/`ci`/
`local` profiles in `SPEC/testing.md`:

- the library has named fixtures committed to the repository;
- the property-test runner passes on the default seed recorded with
  the fixture metadata;
- there is at least one end-to-end case exercising every advertised
  user story in the library's release target (see
  [Releases.md](Releases.md)).

CI for the `core` and `ci` profiles must be green on the conformance
workflow before a library leaves Phase 3.

Record completion by bumping `libraries.yml[L].done_through` to `3`.
