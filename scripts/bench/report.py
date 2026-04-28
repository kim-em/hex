#!/usr/bin/env python3
"""Render a markdown view of one library's benchmark JSONL.

Reads JSONL written by HexArith.Bench (and its HexLLL twin), groups
records by `(family, comparator)`, computes median/min/max wall_nanos
across runs, fits a log-log slope when there are ≥3 distinct params
for a family, and emits a markdown report. JSONL is the source of
truth; this script is just a view.
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any


def load_rows(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open() as f:
        for ln, raw in enumerate(f, 1):
            raw = raw.strip()
            if not raw:
                continue
            try:
                rows.append(json.loads(raw))
            except json.JSONDecodeError as e:
                print(f"warning: {path}:{ln}: bad JSON: {e}", file=sys.stderr)
    return rows


def fmt_ms(ns: int | float) -> str:
    if ns is None:
        return "—"
    ms = ns / 1_000_000.0
    if ms < 1:
        return f"{ms*1000:.1f} µs"
    if ms < 1000:
        return f"{ms:.2f} ms"
    return f"{ms/1000:.2f} s"


def fit_loglog_slope(points: list[tuple[float, float]]) -> float | None:
    """Least-squares slope of log y vs log x. Returns None on bad input."""
    pts = [(x, y) for x, y in points if x > 0 and y > 0]
    if len(pts) < 3:
        return None
    xs = [math.log(x) for x, _ in pts]
    ys = [math.log(y) for _, y in pts]
    n = len(xs)
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    num = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    den = sum((x - mean_x) ** 2 for x in xs)
    if den == 0:
        return None
    return num / den


def verdict(observed: float | None, expected: float | None) -> str:
    if observed is None or expected is None:
        return "insufficient-data"
    if abs(observed - expected) <= 0.5:
        return f"match (Δ={observed-expected:+.2f})"
    return f"off (observed {observed:.2f} vs expected {expected:.2f})"


def render(jsonl_path: Path, library: str, out_path: Path) -> None:
    rows = load_rows(jsonl_path)
    if not rows:
        out_path.write_text(f"# {library} benchmarks\n\n_No JSONL rows; nothing to report._\n")
        return

    # Header context: take from any row (they share meta).
    head = rows[0]
    git_sha = head.get("git_sha", "?")
    hostname = head.get("hostname", "?")
    cpu = head.get("cpu_model") or "?"
    ts = head.get("ts", "?")
    toolchain = head.get("lean_toolchain", "?")
    seed = head.get("seed", "?")

    # Group rows by family. Comparator rows have comparator != null.
    by_family: dict[str, dict[str, Any]] = defaultdict(lambda: {
        "lean": [],          # list of {param, wall_nanos, status, run_index, origin, hash}
        "comparators": defaultdict(list),  # name -> list of dicts
    })
    for r in rows:
        fam = r["family"]
        if r.get("comparator"):
            by_family[fam]["comparators"][r["comparator"]].append(r)
        else:
            by_family[fam]["lean"].append(r)

    lines = [
        f"# {library} benchmarks",
        "",
        f"- Run: `{git_sha}`",
        f"- Machine: {hostname} (CPU: {cpu})",
        f"- Date: {ts}",
        f"- Toolchain: `{toolchain}`",
        f"- Seed: `{seed}`",
        "",
        "Per-family detail follows; the **Summary** table at the end aggregates.",
        "",
    ]

    summary_rows: list[tuple[str, str, str, str, str, str, str]] = []

    for fam, data in sorted(by_family.items()):
        lean_rows = data["lean"]
        if not lean_rows:
            continue
        lines.append(f"## {fam}")
        lines.append("")
        # Group lean rows by param so we can detect ladder vs measured-mode.
        by_param: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for r in lean_rows:
            by_param[r["param"]].append(r)
        params = sorted(by_param)
        if len(params) == 1:
            # measured mode: many runs at one param.
            p = params[0]
            samples = [r["wall_nanos"] for r in by_param[p] if r["status"] == "ok"]
            origin = by_param[p][0]["param_origin"]
            statuses = sorted({r["status"] for r in by_param[p]})
            lines.append(f"- Mode: measured ({len(samples)} runs)")
            lines.append(f"- Parameter: `{p}` (origin: {origin})")
            lines.append(f"- Statuses: {', '.join(statuses)}")
            if samples:
                med = statistics.median(samples)
                lo = min(samples); hi = max(samples)
                lines.append(f"- Wall: median **{fmt_ms(med)}**, min {fmt_ms(lo)}, max {fmt_ms(hi)}")
            else:
                lines.append("- Wall: no `ok` samples")
            slope_str = "—"
        else:
            # ladder mode: one or more runs per param, varying param.
            lines.append(f"- Mode: ladder ({len(params)} rungs)")
            lines.append("")
            lines.append("| param | runs | median | status |")
            lines.append("|---|---|---|---|")
            ladder_pts = []
            for p in params:
                samples = [r["wall_nanos"] for r in by_param[p] if r["status"] == "ok"]
                statuses = sorted({r["status"] for r in by_param[p]})
                med = statistics.median(samples) if samples else None
                lines.append(f"| {p} | {len(by_param[p])} | {fmt_ms(med) if med else '—'} | {','.join(statuses)} |")
                if med is not None:
                    ladder_pts.append((float(p), float(med)))
            slope = fit_loglog_slope(ladder_pts)
            slope_str = f"{slope:.2f}" if slope is not None else "—"
            # Expected slope is metadata we don't currently emit; report's
            # "verdict" field stays "insufficient-data" until we plumb that.
            lines.append("")
            lines.append(f"- Observed log-log slope: **{slope_str}**")

        # Comparators.
        for cmp_name, cmp_rows in sorted(data["comparators"].items()):
            cmp_samples = [r["wall_nanos"] for r in cmp_rows if r["status"] == "ok"]
            if cmp_samples:
                cmp_med = statistics.median(cmp_samples)
                lines.append(f"- Comparator `{cmp_name}`: median {fmt_ms(cmp_med)} ({len(cmp_samples)} runs)")
            else:
                statuses = sorted({r["status"] for r in cmp_rows})
                lines.append(f"- Comparator `{cmp_name}`: no `ok` samples ({','.join(statuses)})")

        # Summary row: use first param's median.
        first_param = params[0]
        lean_samples = [r["wall_nanos"] for r in by_param[first_param] if r["status"] == "ok"]
        lean_med = statistics.median(lean_samples) if lean_samples else None
        cmp_med = None; cmp_name = "—"
        for cn, cr in sorted(data["comparators"].items()):
            cs = [r["wall_nanos"] for r in cr if r["status"] == "ok" and r["param"] == first_param]
            if cs:
                cmp_med = statistics.median(cs); cmp_name = cn
                break
        ratio = (lean_med / cmp_med) if (lean_med and cmp_med) else None
        summary_rows.append((
            fam,
            str(first_param),
            by_param[first_param][0]["param_origin"],
            fmt_ms(lean_med) if lean_med else "—",
            fmt_ms(cmp_med) if cmp_med else "—",
            f"{ratio:.2f}×" if ratio else "—",
            slope_str,
        ))
        lines.append("")

    # Summary
    lines.append("## Summary")
    lines.append("")
    lines.append("| family | param | origin | wall (median) | comparator | ratio (Lean/cmp) | log-log slope |")
    lines.append("|---|---|---|---|---|---|---|")
    for row in summary_rows:
        lines.append("| " + " | ".join(row) + " |")
    lines.append("")
    lines.append("## Honest assessment")
    lines.append("")
    lines.append("_Hand-edit this section after each run with what surprised you,"
                 " what calibration got wrong, and what the report doesn't yet capture._")
    lines.append("")

    out_path.write_text("\n".join(lines))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jsonl", required=True, type=Path)
    ap.add_argument("--library", required=True)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    render(args.jsonl, args.library, args.out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
