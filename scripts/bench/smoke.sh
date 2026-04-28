#!/usr/bin/env bash
# scripts/bench/smoke.sh — CI-style smoke for both bench libraries.
#
# Each library runs at seconds=1 with --max-per-family-seconds 5 and
# --runs 1. Smoke-only families (the ones excluded from the budgeted
# set because of scaffolding limitations — see Families.smokeOnly) are
# also exercised once at tiny share. The run is bounded by an outer
# wallclock cap so a misbehaving family fails CI loudly.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

OUTER_TIMEOUT="${OUTER_TIMEOUT:-60}"

mkdir -p results
ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

export BENCH_GIT_SHA="$(git rev-parse HEAD 2>/dev/null || echo 'unknown')"
export BENCH_TOOLCHAIN="$(cat lean-toolchain 2>/dev/null || echo 'unknown')"
export BENCH_HOSTNAME="$(hostname)"
export BENCH_TS="$ts"

for lib in hex_arith hex_lll; do
  if [[ ! -x "./.lake/build/bin/${lib}_bench" ]]; then
    echo "==> Building ${lib}_bench"
    lake build "${lib}_bench" 2>&1 | tail -5
  fi
  out="results/smoke-${lib}-${ts}.jsonl"
  echo "==> Smoke ${lib} (cap ${OUTER_TIMEOUT}s outer)"
  timeout "$OUTER_TIMEOUT" "./.lake/build/bin/${lib}_bench" 1 \
    --runs 1 --max-per-family-seconds 5 --smoke --out "$out"
  rows=$(wc -l < "$out")
  echo "    emitted $rows JSONL row(s) → $out"
  if [[ "$rows" -lt 1 ]]; then
    echo "    smoke FAILED: no rows emitted" >&2
    exit 1
  fi
done

echo "==> Smoke OK"
