#!/usr/bin/env python3
"""HexArith Python comparator.

Reads the Lean-emitted JSONL (to learn which families ran at which
params), then runs the equivalent operation in Python's stdlib (with
gmpy2 as a richer fallback when available), measuring wall_nanos for
each. Appends one comparator row per Lean row to the JSONL.

JSONL schema is shared with the Lean emitter — see
HexArith/Bench/Driver.lean's `renderRow`.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import math
import sys
import time
from pathlib import Path
from typing import Any, Callable

# SplitMix64 mirror of HexArith.Bench.Random.next, so the comparator
# uses the same input distribution as the Lean side.
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


def next_nonzero_bits(state: int, bits: int) -> tuple[int, int]:
    n, state = next_bits(state, bits)
    return (1 if n == 0 else n), state


def next_range(state: int, n: int) -> tuple[int, int]:
    z, state = splitmix64_next(state)
    return z % n, state


def hash_low64(n: int) -> int:
    return n & _MASK


# ─── per-family Python runners ──────────────────────────────────────────

def run_a1(seed: int, bits: int) -> int:
    a, s1 = next_nonzero_bits(seed, bits)
    b, _ = next_nonzero_bits(s1, bits)
    g, x, y = ext_gcd(a, b)
    return hash_low64(g) ^ (abs(x) & _MASK) ^ (abs(y) & _MASK)


def ext_gcd(a: int, b: int) -> tuple[int, int, int]:
    # Iterative Bezout — recursive version blows the Python stack on
    # 1000+ bit inputs, where extGcd takes ~3000 steps.
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


def run_a2(seed: int, bits: int) -> int:
    a, s1 = next_nonzero_bits(seed, bits)
    n, s2 = next_nonzero_bits(s1, bits)
    p0, _ = next_nonzero_bits(s2, bits)
    p = p0 + 2
    return hash_low64(pow(a, n, p))


A3_MOD = 4294967291  # Barrett


def run_a3(seed: int, n: int) -> int:
    a0, s1 = next_range(seed, A3_MOD)
    b0, _ = next_range(s1, A3_MOD)
    x = a0
    y = b0
    for _ in range(n):
        x = (x * y) % A3_MOD
    return x & _MASK


# ─── driver ─────────────────────────────────────────────────────────────

FAMILIES: dict[str, Callable[[int, int], int]] = {
    "A1.nat-extgcd": run_a1,
    "A2.nat-powmod": run_a2,
    "A3.barrett-mulmod": run_a3,
    # A4 not implemented here — Lean side is smoke-only because of a
    # scaffolding limitation, comparator would dominate the noise.
}


def time_one(fn: Callable[[int, int], int], seed: int, param: int) -> tuple[int, int]:
    t0 = time.perf_counter_ns()
    h = fn(seed, param)
    t1 = time.perf_counter_ns()
    return h, t1 - t0


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
    out["run_index"] = lean_row.get("run_index", 0)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", required=True, type=Path,
                    help="JSONL produced by hex_arith_bench")
    ap.add_argument("--append", required=True, type=Path,
                    help="Append comparator rows here (often same as --in)")
    args = ap.parse_args()

    py_version = f"python-{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}"

    rows = [json.loads(l) for l in args.inp.read_text().splitlines() if l.strip()]
    appended = 0
    out_lines: list[str] = []
    for r in rows:
        if r.get("comparator"):
            continue  # don't comparate a comparator row
        if r.get("status") != "ok":
            continue
        fam = r["family"]
        fn = FAMILIES.get(fam)
        if fn is None:
            continue
        seed = int(r["seed"])
        param = int(r["param"])
        h, wall = time_one(fn, seed, param)
        out_lines.append(json.dumps(make_comparator_row(r, wall, h, "python-stdlib", py_version)))
        appended += 1

    if out_lines:
        with args.append.open("a") as f:
            for ln in out_lines:
                f.write(ln + "\n")
    print(f"appended {appended} comparator row(s)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
