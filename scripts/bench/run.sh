#!/usr/bin/env bash
# scripts/bench/run.sh <library> <seconds> [extra-args …]
#
# Drives one benchmark library end-to-end:
#  1. Builds the bench exe.
#  2. Captures run metadata into env vars.
#  3. Runs the bench, streaming JSONL to results/.
#  4. Runs the matching Python comparator (if available) and appends rows.
#  5. Renders the markdown report into HexManual/Benchmarks/<Lib>.md.
#
# Library is one of: hex_arith, hex_lll.
set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "usage: $0 <hex_arith|hex_lll> <seconds> [--ladder] [--smoke] [--runs N]" >&2
  exit 2
fi

lib="$1"; shift
seconds="$1"; shift
extra_args=("$@")

case "$lib" in
  hex_arith) lib_pretty="HexArith" ; comparator="python_arith.py" ;;
  hex_lll)   lib_pretty="HexLLL"   ; comparator="fpylll_lll.py" ;;
  *) echo "unknown library: $lib (expected hex_arith or hex_lll)" >&2; exit 2 ;;
esac

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

mkdir -p results
ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
out_jsonl="results/${lib}-${ts}.jsonl"

export BENCH_GIT_SHA="$(git rev-parse HEAD 2>/dev/null || echo 'unknown')"
export BENCH_TOOLCHAIN="$(cat lean-toolchain 2>/dev/null || echo 'unknown')"
export BENCH_HOSTNAME="$(hostname)"
export BENCH_TS="$ts"
# CPU model is best-effort: works on Linux via /proc/cpuinfo, otherwise unset.
if [[ -r /proc/cpuinfo ]]; then
  cpu="$(grep -m1 '^model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//')"
  [[ -n "$cpu" ]] && export BENCH_CPU_MODEL="$cpu"
fi

echo "==> Building ${lib}_bench"
lake build "${lib}_bench" 2>&1 | grep -E '✔|✖|error|warning' | tail -20

echo "==> Running Lean bench (${seconds}s budget)"
"./.lake/build/bin/${lib}_bench" "$seconds" --out "$out_jsonl" "${extra_args[@]}"

# Comparator is optional; SKIP_COMPARATOR=1 disables.
comparator_path="scripts/bench/external/${comparator}"
if [[ "${SKIP_COMPARATOR:-0}" != "1" && -x "$comparator_path" ]]; then
  echo "==> Running comparator ${comparator}"
  if "$comparator_path" --in "$out_jsonl" --append "$out_jsonl" 2>&1; then
    echo "    comparator OK"
  else
    echo "    comparator failed (continuing)"
  fi
elif [[ "${SKIP_COMPARATOR:-0}" != "1" ]]; then
  echo "==> No executable comparator at $comparator_path; skipping"
fi

echo "==> Rendering report → HexManual/Benchmarks/${lib_pretty}.md"
python3 scripts/bench/report.py --jsonl "$out_jsonl" --library "$lib_pretty" \
  --out "HexManual/Benchmarks/${lib_pretty}.md"

echo "==> Done. JSONL: $out_jsonl  Report: HexManual/Benchmarks/${lib_pretty}.md"
