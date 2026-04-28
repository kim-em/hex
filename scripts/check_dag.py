#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re
import sys

from libgraph import (
    EXTERNAL_IMPORT_ROOTS,
    KNOWN_EXCEPTIONS,
    check_lakefile_alignment,
    library_owner_for_path,
    load_lakefile_libs,
    load_libraries,
    reachable_dependencies,
    topological_order,
)


IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")


def project_lean_files(root: Path) -> list[Path]:
    files = []
    for path in root.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        files.append(path.relative_to(root))
    return sorted(files)


def import_roots(line: str) -> list[str]:
    match = IMPORT_RE.match(line.split("--", 1)[0].rstrip())
    if not match:
        return []
    roots = []
    for token in match.group(1).replace(",", " ").split():
        token = token.strip()
        if token:
            roots.append(token.split(".", 1)[0])
    return roots


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    errors: list[str] = []

    try:
        libraries = load_libraries(root / "libraries.yml")
        lakefile_libs = load_lakefile_libs(root)
        topological_order(libraries)
        reachable = reachable_dependencies(libraries)
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1

    errors.extend(check_lakefile_alignment(libraries, lakefile_libs))

    for name in list(libraries) + sorted(KNOWN_EXCEPTIONS):
        if not (root / f"{name}.lean").exists():
            errors.append(f"missing root file {name}.lean")

    for rel_path in project_lean_files(root):
        owner = library_owner_for_path(rel_path, libraries)
        if owner is None:
            continue
        path = root / rel_path
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for imported_root in import_roots(line):
                if imported_root == owner:
                    continue
                if imported_root == "Mathlib":
                    if owner != "HexManual" and not libraries[owner].mathlib:
                        errors.append(
                            f"{rel_path}:{line_no} imports Mathlib but {owner} is not a mathlib bridge"
                        )
                    continue
                if imported_root == "Verso":
                    if owner != "HexManual":
                        errors.append(f"{rel_path}:{line_no} imports Verso outside HexManual")
                    continue
                if imported_root in libraries:
                    allowed = reachable[owner] if owner in libraries else set(libraries)
                    if owner == "HexManual":
                        allowed = set(libraries)
                    if imported_root not in allowed:
                        errors.append(
                            f"{rel_path}:{line_no} imports {imported_root} without a dependency path from {owner}"
                        )
                    continue
                if imported_root in EXTERNAL_IMPORT_ROOTS:
                    continue

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
