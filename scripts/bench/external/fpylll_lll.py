#!/usr/bin/env python3
"""HexLLL Python comparator using fpylll (if available).

Reads Lean-emitted JSONL, regenerates the same matrix using the
mirrored SplitMix64 from [python_arith.py](./python_arith.py), runs
fpylll's LLL.reduction on it, times it, and appends comparator rows.

If fpylll is not installed, we emit nothing (run.sh continues and the
report shows "comparator unavailable"). This script exits 0 either way.
"""

from __future__ import annotations

import argparse
import datetime
import json
import sys
import time
from pathlib import Path
from typing import Any

_MASK = (1 << 64) - 1


def splitmix64_next(state: int) -> tuple[int, int]:
    state = (state + 0x9E3779B97F4A7C15) & _MASK
    z = state
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & _MASK
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & _MASK
    z = z ^ (z >> 31)
    return z, state


def next_bits(state: int, bits: int) -> tuple[int, int]:
    if bits <= 0:
        return 0, state
    n_chunks = (bits + 63) // 64
    acc = 0
    for _ in range(n_chunks):
        z, state = splitmix64_next(state)
        acc = (acc << 64) | z
    total = n_chunks * 64
    if total > bits:
        acc >>= total - bits
    return acc, state


def next_signed_bits(state: int, bits: int) -> tuple[int, int]:
    n, state = next_bits(state, bits + 1)
    sign = n & 1
    mag = n >> 1
    return (mag if sign == 0 else -mag), state


def gen_matrix(n: int, bits: int, seed: int) -> list[list[int]]:
    state = seed
    rows: list[list[int]] = []
    for _ in range(n):
        row: list[int] = []
        for _ in range(n):
            v, state = next_signed_bits(state, bits)
            row.append(v)
        rows.append(row)
    return rows


def snap_l1_dim(n: int) -> int:
    for rung in (4, 6, 8, 12, 16, 20, 24):
        if n <= rung:
            return rung
    return 24


def hash_low64_matrix(M: list[list[int]]) -> int:
    h = 0
    for row in M:
        for e in row:
            h ^= abs(e) & _MASK
    return h


def run_l1(fpylll_mod, seed: int, n_param: int) -> tuple[int, int]:
    n = snap_l1_dim(n_param)
    mat = gen_matrix(n, 20, seed)
    IM = fpylll_mod.IntegerMatrix.from_matrix(mat)
    t0 = time.perf_counter_ns()
    fpylll_mod.LLL.reduction(IM, delta=0.75)
    t1 = time.perf_counter_ns()
    reduced = [[IM[i, j] for j in range(n)] for i in range(n)]
    return hash_low64_matrix(reduced), t1 - t0


def run_l2(fpylll_mod, seed: int, bits: int) -> tuple[int, int]:
    n = 6
    mat = gen_matrix(n, bits, seed)
    IM = fpylll_mod.IntegerMatrix.from_matrix(mat)
    t0 = time.perf_counter_ns()
    fpylll_mod.LLL.reduction(IM, delta=0.75)
    t1 = time.perf_counter_ns()
    reduced = [[IM[i, j] for j in range(n)] for i in range(n)]
    return hash_low64_matrix(reduced), t1 - t0


FAMILIES = {"L1.uniform-dim-sweep": run_l1, "L2.arith-bit-sweep": run_l2}


def make_comparator_row(lean_row: dict[str, Any], wall_nanos: int, h: int,
                        comparator: str, version: str) -> dict[str, Any]:
    out = dict(lean_row)
    out["wall_nanos"] = wall_nanos
    out["result_hash"] = f"0x{h:x}"
    out["comparator"] = comparator
    out["comparator_version"] = version
    out["status"] = "ok"
    out["error"] = None
    out["ts"] = datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", required=True, type=Path)
    ap.add_argument("--append", required=True, type=Path)
    args = ap.parse_args()

    try:
        import fpylll
    except Exception as e:
        print(f"fpylll not available: {e}; skipping comparator rows", file=sys.stderr)
        return 0

    version = getattr(fpylll, "__version__", "unknown")
    rows = [json.loads(l) for l in args.inp.read_text().splitlines() if l.strip()]
    out_lines: list[str] = []
    for r in rows:
        if r.get("comparator"):
            continue
        if r.get("status") != "ok":
            continue
        fn = FAMILIES.get(r["family"])
        if fn is None:
            continue
        h, wall = fn(fpylll, int(r["seed"]), int(r["param"]))
        out_lines.append(json.dumps(make_comparator_row(r, wall, h, "fpylll", version)))

    if out_lines:
        with args.append.open("a") as f:
            for ln in out_lines:
                f.write(ln + "\n")
    print(f"appended {len(out_lines)} comparator row(s)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
