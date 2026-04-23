#!/usr/bin/env python3
from __future__ import annotations

import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
import tomllib


ROOT = Path(__file__).resolve().parent.parent
LIBRARIES_YML = ROOT / "libraries.yml"
LAKEFILE = ROOT / "lakefile.toml"
KNOWN_TOML_EXCEPTIONS = {"HexManual"}

PHASES = {
    1: "library scaffolding",
    2: "scaffolding review",
    3: "conformance testing",
    4: "performance & benchmarking",
    5: "implementation work loop",
    6: "proof polishing",
    7: "user-facing documentation",
}

RELEASES = {
    1: {
        "libraries": ["HexModArith", "HexPoly", "HexPolyFp", "HexGfqRing", "HexGfqField", "HexGF2"],
        "example": ROOT / "Examples" / "Release1.lean",
    },
    2: {
        "libraries": [
            "HexModArith",
            "HexPoly",
            "HexPolyFp",
            "HexGfqRing",
            "HexGfqField",
            "HexGF2",
            "HexBerlekamp",
            "HexBerlekampMathlib",
            "HexConway",
            "HexGfq",
        ],
        "example": ROOT / "Examples" / "Release2.lean",
    },
    3: {
        "libraries": [
            "HexModArith",
            "HexPoly",
            "HexPolyFp",
            "HexGfqRing",
            "HexGfqField",
            "HexGF2",
            "HexBerlekamp",
            "HexBerlekampMathlib",
            "HexConway",
            "HexGfq",
            "HexPolyZ",
            "HexHensel",
            "HexBerlekampZassenhaus",
        ],
        "example": ROOT / "Examples" / "Release3.lean",
    },
    4: {
        "libraries": [
            "HexModArith",
            "HexPoly",
            "HexPolyFp",
            "HexGfqRing",
            "HexGfqField",
            "HexGF2",
            "HexBerlekamp",
            "HexBerlekampMathlib",
            "HexConway",
            "HexGfq",
            "HexPolyZ",
            "HexHensel",
            "HexBerlekampZassenhaus",
            "HexLLL",
        ],
        "example": ROOT / "Examples" / "Release4.lean",
    },
}


class ParseError(ValueError):
    pass


@dataclass(frozen=True)
class PhaseState:
    library: str
    done_through: int
    next_phase: int | None
    ready: bool
    blockers: tuple[str, ...]


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
    return libraries


def validate_against_lakefile(libraries: dict[str, dict[str, object]]) -> None:
    with LAKEFILE.open("rb") as handle:
        lakefile = tomllib.load(handle)
    lean_libs = lakefile.get("lean_lib", [])
    if not isinstance(lean_libs, list):
        raise ParseError("lakefile.toml is missing [[lean_lib]] entries")
    names = {entry["name"] for entry in lean_libs if isinstance(entry, dict) and "name" in entry}
    missing = sorted(set(libraries) - names)
    extra = sorted(name for name in names if name not in libraries and name not in KNOWN_TOML_EXCEPTIONS)
    if missing or extra:
        chunks = []
        if missing:
            chunks.append(f"missing from lakefile.toml: {', '.join(missing)}")
        if extra:
            chunks.append(f"extra in lakefile.toml: {', '.join(extra)}")
        raise ParseError("; ".join(chunks))


def spec_path(library: str) -> str:
    kebab = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "-", library)
    kebab = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", "-", kebab)
    return f"SPEC/Libraries/{kebab.lower()}.md"


def evaluate_phase(library: str, data: dict[str, object], libraries: dict[str, dict[str, object]]) -> PhaseState:
    done_through = int(data["done_through"])
    if done_through >= 7:
        return PhaseState(library, done_through, None, False, ())

    next_phase = done_through + 1
    blockers: list[str] = []
    if next_phase > 1 and done_through < next_phase - 1:
        blockers.append(f"{library}.done_through ≥ {next_phase - 1}")
    if next_phase in {1, 3, 4}:
        for dep in data["deps"]:
            dep_done = int(libraries[dep]["done_through"])
            if dep_done < next_phase:
                blockers.append(f"{dep}.done_through ≥ {next_phase}")
    return PhaseState(library, done_through, next_phase, not blockers, tuple(blockers))


def print_phase_entry(state: PhaseState) -> None:
    assert state.next_phase is not None
    print(f"  {state.library} -> Phase {state.next_phase} ({PHASES[state.next_phase]})")
    print(f"    spec: {spec_path(state.library)}")
    print(f"    plan: PLAN/Phase{state.next_phase}.md")
    print(f"    on complete: libraries.yml {state.library}.done_through: {state.next_phase}")


def print_blocked_entry(state: PhaseState) -> None:
    assert state.next_phase is not None
    print(f"  {state.library} -> Phase {state.next_phase}")
    print(f"    waiting on: {', '.join(state.blockers)}")


def status_all(libraries: dict[str, dict[str, object]]) -> int:
    ready: list[PhaseState] = []
    blocked: list[PhaseState] = []
    fully_done: list[str] = []

    for library, data in libraries.items():
        state = evaluate_phase(library, data, libraries)
        if state.next_phase is None:
            fully_done.append(library)
        elif state.ready:
            ready.append(state)
        else:
            blocked.append(state)

    print("Ready (dispatch issues in parallel):")
    print()
    if ready:
        for state in ready:
            print_phase_entry(state)
            print()
    else:
        print("  (none)")
        print()

    print("Blocked:")
    print()
    if blocked:
        for state in blocked:
            print_blocked_entry(state)
            print()
    else:
        print("  (none)")
        print()

    print("Fully done:")
    if fully_done:
        for library in fully_done:
            print(f"  {library}")
    else:
        print("  (none yet)")
    return 0


def status_one(libraries: dict[str, dict[str, object]], library: str) -> int:
    if library not in libraries:
        print(f"unknown library: {library}", file=sys.stderr)
        return 1
    state = evaluate_phase(library, libraries[library], libraries)
    print(f"{library}")
    print(f"  done_through: {state.done_through}")
    if state.next_phase is None:
        print("  next: fully done")
        return 0
    print(f"  next: Phase {state.next_phase} ({PHASES[state.next_phase]})")
    print(f"  spec: {spec_path(library)}")
    print(f"  plan: PLAN/Phase{state.next_phase}.md")
    if state.ready:
        print("  status: ready")
    else:
        print(f"  status: blocked by {', '.join(state.blockers)}")
    return 0


def release_status(libraries: dict[str, dict[str, object]], release_number: int) -> int:
    release = RELEASES.get(release_number)
    if release is None:
        print(f"unknown release: {release_number}", file=sys.stderr)
        return 1

    missing = [name for name in release["libraries"] if int(libraries[name]["done_through"]) < 7]
    example = release["example"]
    exists = example.exists()
    builds = False
    if exists:
        result = subprocess.run(
            ["lake", "env", "lean", str(example)],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        builds = result.returncode == 0

    print(f"Release {release_number}")
    if missing:
        print("  missing libraries:")
        for library in missing:
            print(f"    {library}: needs done_through >= 7")
    else:
        print("  missing libraries: none")
    print(f"  integration example: {example.relative_to(ROOT)}")
    print(f"  example exists: {'yes' if exists else 'no'}")
    print(f"  example builds: {'yes' if builds else 'no'}")
    print(f"  ready: {'yes' if not missing and builds else 'no'}")
    return 0


def main(argv: list[str]) -> int:
    try:
        libraries = parse_libraries(LIBRARIES_YML)
        validate_against_lakefile(libraries)
    except (OSError, tomllib.TOMLDecodeError, ParseError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if len(argv) == 1:
        return status_all(libraries)
    if len(argv) == 2:
        return status_one(libraries, argv[1])
    if len(argv) == 3 and argv[1] == "release":
        try:
            release_number = int(argv[2])
        except ValueError:
            print(f"invalid release number: {argv[2]}", file=sys.stderr)
            return 1
        return release_status(libraries, release_number)

    print("usage: status.py [<Library> | release <N>]", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
