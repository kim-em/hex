# hex — Workflow Plan

You are a planner agent. Your job is to **survey project state and
dispatch GitHub issues** for worker agents to pick up. You do not
implement — workers do.

## Start of cycle

1. Merge all mergeable + green open PRs before creating new work.
   Details in [PLAN/Conventions.md](PLAN/Conventions.md).
2. List current open GitHub issues. These are your ground truth for
   work already in flight; you will cross-reference against the
   status survey below to avoid duplicate dispatch.

## Bootstrap check

If `scripts/status.py` does not yet exist, the repo is pre-bootstrap.
Go straight to [PLAN/Phase0.md](PLAN/Phase0.md) — Phase 0 is a single
critical-path issue handled by one worker. Dispatch (or execute) it
and wait for it to land before returning here.

## Survey and dispatch

Otherwise, run `scripts/status.py`. It lists every `(library, phase)`
pair that is currently ready for work, and for each pair names:

- the **SPEC file**: `SPEC/Libraries/hex-foo.md` — the library's design;
- the **PLAN file**: `PLAN/PhaseK.md` — the phase rules and exit criteria;
- the `libraries.yml` bump expected when the phase completes.

Multiple pairs are ready at once — that is the point of the
phase-dependency rules. Dispatch in parallel rather than serialising.
For each ready pair, decide whether to create new issues using:

- **Existing open-issue coverage.** If open issues already cover a
  pair adequately, skip it this cycle.
- **Worker capacity headroom.** Don't dispatch more than workers can
  reasonably pick up before the next planner cycle.

For each pair you do choose to dispatch:

1. Read `SPEC/Libraries/hex-foo.md` for the library's design (and
   `SPEC/SPEC.md` + any cross-cutting SPEC files it links — e.g.
   `SPEC/testing.md` for Phase 3 — if you haven't already this session).
2. Read `PLAN/PhaseK.md` for the phase's scope and exit criteria.
3. **Add more narrow GitHub issues** advancing the pair's work. You
   are not writing a complete decomposition for the `(library,
   phase)` pair in one go — you are adding the next batch of work
   units for workers to pick up, on top of whatever issues already
   exist. Follow the issue-creation rules in
   [PLAN/Conventions.md](PLAN/Conventions.md) (canonical body
   shape, narrow scope, `depends-on:` dependency syntax).

## Once per session

Read [PLAN/Conventions.md](PLAN/Conventions.md) for conventions you
shouldn't rediscover each time: naming, FFI, PR auto-merge, per-turn
progress files, `SPEC/` immutability, the phase-dependency rule
table, and how `libraries.yml` relates to `status/` tokens and
GitHub issues.

## Key files

- [SPEC/SPEC.md](SPEC/SPEC.md) and [SPEC/Libraries/](SPEC/Libraries/)
  — *what* to build.
- [libraries.yml](libraries.yml) — per-library phase counter.
- [PLAN/](PLAN/) — *how* to execute each phase; immutable reference.
- [PLAN/Releases.md](PLAN/Releases.md) — release readiness predicate.
