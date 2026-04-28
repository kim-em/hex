#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from collections import deque
from pathlib import Path
import tomllib


ROOT = Path(__file__).resolve().parent.parent
LIBRARIES_YML = ROOT / "libraries.yml"
LAKEFILE = ROOT / "lakefile.toml"
KNOWN_TOML_EXCEPTIONS = {"HexManual"}
CORE_IMPORT_PREFIXES = {"Init", "Lean", "Lake", "Std"}


class ParseError(ValueError):
    pass


def parse_libraries(path: Path) -> dict[str, dict[str, object]]:
    libraries: dict[str, dict[str, object]] = {}
    current: str | None = None
    in_libraries = False

    for line_no, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw_line.split("#", 1)[0].rstrip()
        if not line:
            continue
        if line == "libraries:":
            in_libraries = True
            continue
        if not in_libraries:
            continue

        top_match = re.fullmatch(r"  ([A-Za-z0-9]+):", line)
        if top_match:
            current = top_match.group(1)
            if current in libraries:
                raise ParseError(f"duplicate library {current!r} on line {line_no}")
            libraries[current] = {}
            continue

        field_match = re.fullmatch(r"    (deps|mathlib|done_through):\s*(.+)", line)
        if not field_match or current is None:
            raise ParseError(f"unsupported syntax on line {line_no}: {raw_line}")

        field, value = field_match.groups()
        if field == "deps":
            deps_match = re.fullmatch(r"\[(.*)\]", value)
            if not deps_match:
                raise ParseError(f"invalid deps list on line {line_no}")
            inner = deps_match.group(1).strip()
            deps = [] if not inner else [item.strip() for item in inner.split(",")]
            libraries[current][field] = deps
        elif field == "mathlib":
            if value not in {"true", "false"}:
                raise ParseError(f"invalid boolean on line {line_no}")
            libraries[current][field] = value == "true"
        else:
            try:
                libraries[current][field] = int(value)
            except ValueError as exc:
                raise ParseError(f"invalid integer on line {line_no}") from exc

    for library, data in libraries.items():
        missing = {"deps", "mathlib", "done_through"} - data.keys()
        if missing:
            raise ParseError(f"{library} missing fields: {', '.join(sorted(missing))}")
        if not isinstance(data["deps"], list):
            raise ParseError(f"{library} has malformed deps")
    return libraries


def load_lakefile(path: Path) -> dict[str, object]:
    with path.open("rb") as handle:
        return tomllib.load(handle)


def collect_structural_errors(
    libraries: dict[str, dict[str, object]], lakefile: dict[str, object]
) -> list[str]:
    errors: list[str] = []
    graph = {name: list(data["deps"]) for name, data in libraries.items()}

    for library, deps in graph.items():
        for dep in deps:
            if dep not in libraries:
                errors.append(f"{library} depends on unknown library {dep}")

    indegree = {name: 0 for name in libraries}
    for library, deps in graph.items():
        for dep in deps:
            if dep in libraries:
                indegree[library] += 1
    queue = deque([name for name, degree in indegree.items() if degree == 0])
    seen = 0
    reverse_graph = {name: [] for name in libraries}
    for library, deps in graph.items():
        for dep in deps:
            if dep in reverse_graph:
                reverse_graph[dep].append(library)
    while queue:
        library = queue.popleft()
        seen += 1
        for child in reverse_graph[library]:
            indegree[child] -= 1
            if indegree[child] == 0:
                queue.append(child)
    if seen != len(libraries):
        errors.append("libraries.yml dependency graph is cyclic")

    lean_libs = lakefile.get("lean_lib", [])
    if not isinstance(lean_libs, list):
        errors.append("lakefile.toml is missing [[lean_lib]] entries")
        return errors

    lean_names = set()
    for entry in lean_libs:
        if not isinstance(entry, dict) or "name" not in entry:
            errors.append("lakefile.toml contains a malformed [[lean_lib]] entry")
            continue
        lean_names.add(entry["name"])

    for library in libraries:
        if library not in lean_names:
            errors.append(f"{library} is missing from lakefile.toml")
    for lean_name in lean_names:
        if lean_name not in libraries and lean_name not in KNOWN_TOML_EXCEPTIONS:
            errors.append(f"{lean_name} appears in lakefile.toml but not libraries.yml")

    for library in set(libraries) | KNOWN_TOML_EXCEPTIONS:
        if not (ROOT / f"{library}.lean").exists():
            errors.append(f"missing root file {library}.lean")

    return errors


def library_for_path(path: Path, libraries: set[str]) -> str | None:
    if path.parent == ROOT and path.stem in libraries | KNOWN_TOML_EXCEPTIONS:
        return path.stem
    top = path.relative_to(ROOT).parts[0]
    if top in libraries | KNOWN_TOML_EXCEPTIONS:
        return top
    return None


def imported_library(module_name: str, libraries: set[str]) -> str | None:
    head = module_name.split(".", 1)[0]
    if head in libraries | KNOWN_TOML_EXCEPTIONS:
        return head
    return None


def dep_closure(libraries: dict[str, dict[str, object]], name: str) -> set[str]:
    """Transitive closure of `name`'s deps in `libraries.yml` (excludes `name` itself).

    An import is allowed from `owner` to any library reachable in this
    closure, matching Lake's actual symbol-visibility semantics. See
    PLAN/Phase0.md "Import boundary checks".
    """
    seen: set[str] = set()
    stack = list(libraries[name]["deps"])
    while stack:
        dep = stack.pop()
        if dep in seen or dep not in libraries:
            continue
        seen.add(dep)
        stack.extend(libraries[dep]["deps"])
    return seen


def collect_import_errors(libraries: dict[str, dict[str, object]]) -> list[str]:
    errors: list[str] = []
    library_names = set(libraries)
    tracked_libraries = library_names | KNOWN_TOML_EXCEPTIONS

    for path in ROOT.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        owner = library_for_path(path, library_names)
        if owner is None:
            continue
        allowed = dep_closure(libraries, owner) if owner in libraries else set()
        if owner == "HexManual":
            allowed = set(library_names)
        allowed.add(owner)

        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            match = re.match(r"^\s*import\s+(.+)$", line)
            if not match:
                continue
            modules = match.group(1).split()
            for module_name in modules:
                head = module_name.split(".", 1)[0]
                if head in CORE_IMPORT_PREFIXES:
                    continue
                if head == "Mathlib":
                    if owner == "HexManual":
                        errors.append(
                            f"{path.relative_to(ROOT)}:{line_no} imports Mathlib directly from HexManual"
                        )
                    elif owner in libraries and not libraries[owner]["mathlib"]:
                        errors.append(
                            f"{path.relative_to(ROOT)}:{line_no} imports Mathlib from non-mathlib library {owner}"
                        )
                    continue
                if head == "Verso":
                    if owner != "HexManual":
                        errors.append(
                            f"{path.relative_to(ROOT)}:{line_no} imports Verso outside HexManual"
                        )
                    continue
                imported = imported_library(module_name, library_names)
                if imported is None:
                    continue
                if imported not in allowed:
                    errors.append(
                        f"{path.relative_to(ROOT)}:{line_no} imports {module_name} outside {owner}'s boundary"
                    )
                if imported == "HexManual" and owner != "HexManual":
                    errors.append(
                        f"{path.relative_to(ROOT)}:{line_no} imports HexManual from {owner}"
                    )
        if owner not in tracked_libraries:
            errors.append(f"could not determine owner for {path.relative_to(ROOT)}")

    return errors


def main() -> int:
    try:
        libraries = parse_libraries(LIBRARIES_YML)
        lakefile = load_lakefile(LAKEFILE)
    except (OSError, tomllib.TOMLDecodeError, ParseError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    errors = collect_structural_errors(libraries, lakefile)
    errors.extend(collect_import_errors(libraries))
    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
