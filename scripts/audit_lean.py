#!/usr/bin/env python3
"""Reject proof placeholders and project axioms in repository Lean source."""

from __future__ import annotations

import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
# This metaprogram intentionally refers to `sorryAx` in order to reject it after elaboration.
# It is itself covered by the kernel-level audit invoked from `YangMills.lean`.
SEMANTIC_AUDIT_MODULES = {
    Path("YangMills/Audit.lean"),
}
FORBIDDEN = {
    "sorry": re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])"),
    "admit": re.compile(r"(?<![A-Za-z0-9_])admit(?![A-Za-z0-9_])"),
    "sorryAx": re.compile(r"(?<![A-Za-z0-9_])sorryAx(?![A-Za-z0-9_])"),
    "axiom-like declaration": re.compile(
        r"^\s*(?:(?:private|protected|unsafe|noncomputable)\s+)*"
        r"(?:axiom|axioms|constant|constants)\s",
        re.MULTILINE,
    ),
}


def main() -> int:
    failures: list[str] = []
    files: list[Path] = []
    ignored = {".git", ".lake", ".pi-subagents"}
    for directory, names, filenames in os.walk(ROOT, followlinks=False):
        current = Path(directory)
        kept_names: list[str] = []
        for name in names:
            path = current / name
            if name in ignored:
                continue
            if path.is_symlink():
                failures.append(f"{path.relative_to(ROOT)}: forbidden source-tree symlink")
            else:
                kept_names.append(name)
        names[:] = kept_names
        for name in filenames:
            if not name.endswith(".lean"):
                continue
            path = current / name
            if path.is_symlink():
                failures.append(f"{path.relative_to(ROOT)}: forbidden Lean-source symlink")
            else:
                files.append(path)
    files.sort()
    if not files:
        print("ERROR no Lean source files found", file=sys.stderr)
        return 1
    audited = 0
    for path in files:
        if path.relative_to(ROOT) in SEMANTIC_AUDIT_MODULES:
            continue
        audited += 1
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            failures.append(f"{path.relative_to(ROOT)}: unreadable UTF-8 Lean source: {error}")
            continue
        for label, pattern in FORBIDDEN.items():
            for match in pattern.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(f"{path.relative_to(ROOT)}:{line}: forbidden {label}")
    if failures:
        print("\n".join(f"ERROR {failure}" for failure in failures), file=sys.stderr)
        return 1
    print(
        f"PASS source-audited {audited} Lean file(s); "
        "semantic namespace audit is enforced by YangMills.lean"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
