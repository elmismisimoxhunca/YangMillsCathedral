#!/usr/bin/env python3
"""Verify that the standalone checker contains exactly its declared Lean dependency closure."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "CHECKER_FILES.txt"
ROOT_MODULE = ROOT / "YangMillsChecker.lean"
AUXILIARY_LEAN = {Path("YangMillsChecker.lean"), Path("CandidateTemplate.lean")}
SEMANTIC_AUDIT_MODULE = Path("YangMills/Audit.lean")
FORBIDDEN_TRACKS = (
    "TwoDimensional",
    "FourDimensional",
    "Renormalization/",
    "Lattice/",
)
FORBIDDEN_SOURCE = {
    "sorry": re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])"),
    "admit": re.compile(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])"),
    "sorryAx": re.compile(r"(?<![A-Za-z0-9_])sorryAx(?![A-Za-z0-9_])"),
    "axiom-like declaration": re.compile(
        r"^\s*(?:(?:private|protected|unsafe|noncomputable)\s+)*"
        r"(?:axiom|axioms|constant|constants)\s",
        re.MULTILINE,
    ),
}
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def fail(message: str, failures: list[str]) -> None:
    failures.append(message)


def main() -> int:
    failures: list[str] = []
    if not MANIFEST.is_file() or not ROOT_MODULE.is_file():
        print("ERROR missing checker manifest or root module", file=sys.stderr)
        return 1

    entries = [line.strip() for line in MANIFEST.read_text().splitlines() if line.strip()]
    if entries != sorted(set(entries)):
        fail("CHECKER_FILES.txt must be sorted and duplicate-free", failures)
    declared = {Path(entry) for entry in entries}
    actual = {
        path.relative_to(ROOT)
        for path in (ROOT / "YangMills").rglob("*.lean")
        if path.is_file()
    }
    for path in sorted(declared - actual):
        fail(f"declared file is missing: {path}", failures)
    for path in sorted(actual - declared):
        fail(f"undeclared Lean file: {path}", failures)

    for relative in sorted(AUXILIARY_LEAN):
        if not (ROOT / relative).is_file():
            fail(f"missing auxiliary Lean file: {relative}", failures)

    total_lines = 0
    project_imports: dict[Path, set[Path]] = {}
    for relative in sorted(actual | AUXILIARY_LEAN):
        path = ROOT / relative
        if path.is_symlink():
            fail(f"source symlink is forbidden: {relative}", failures)
            continue
        text = path.read_text(encoding="utf-8")
        total_lines += text.count("\n") + 1
        rendered = relative.as_posix()
        for marker in FORBIDDEN_TRACKS:
            if marker in rendered:
                fail(f"frozen research track entered checker closure: {relative}", failures)
        if relative != SEMANTIC_AUDIT_MODULE:
            for label, pattern in FORBIDDEN_SOURCE.items():
                for match in pattern.finditer(text):
                    line = text.count("\n", 0, match.start()) + 1
                    fail(f"{relative}:{line}: forbidden {label}", failures)
        relative_imports: set[Path] = set()
        for match in IMPORT.finditer(text):
            for imported in match.group(1).split():
                if not imported.startswith("YangMills."):
                    continue
                target = module_path(imported)
                relative_imports.add(target)
                if target not in declared:
                    line = text.count("\n", 0, match.start()) + 1
                    fail(f"{relative}:{line}: project import outside closure: {imported}", failures)
                for marker in FORBIDDEN_TRACKS:
                    if marker in imported:
                        fail(f"{relative}: frozen-track import: {imported}", failures)
        project_imports[relative] = relative_imports

    required_roots = {
        "YangMills.Audit",
        "YangMills.Dimensions.ThreeDimensionalSU2GaugeGroupProbes",
        "YangMills.Dimensions.ThreeDimensionalSU2ExistenceMassGapAcceptanceProbes",
        "YangMills.Dimensions.ThreeDimensionalSU2PluginCheckerProbes",
    }
    root_imports: set[str] = set()
    for match in IMPORT.finditer(ROOT_MODULE.read_text(encoding="utf-8")):
        root_imports.update(match.group(1).split())
    for module in sorted(required_roots - root_imports):
        fail(f"root module does not import required audit surface: {module}", failures)
    if "CandidateTemplate" not in root_imports:
        fail("root module does not import the conditional candidate template", failures)

    reachable: set[Path] = set()
    stack = [module_path(module) for module in root_imports if module.startswith("YangMills.")]
    while stack:
        relative = stack.pop()
        if relative in reachable or relative not in declared:
            continue
        reachable.add(relative)
        stack.extend(project_imports.get(relative, set()))
    for relative in sorted(declared - reachable):
        fail(f"manifest file is not reachable from the checker root: {relative}", failures)

    if failures:
        print("\n".join(f"ERROR {message}" for message in failures), file=sys.stderr)
        return 1
    print(
        f"PASS standalone checker closure: {len(declared)} project modules, "
        f"{total_lines} Lean lines, no frozen-track imports, placeholders, or project axioms"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
