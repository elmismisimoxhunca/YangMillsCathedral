#!/usr/bin/env python3
"""Verify that the extracted checker snapshot matches its monorepo source modules."""

from __future__ import annotations

from pathlib import Path
import hashlib
import sys

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "checker"
MANIFEST = CHECKER / "CHECKER_FILES.txt"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    failures: list[str] = []
    entries = [Path(line.strip()) for line in MANIFEST.read_text().splitlines() if line.strip()]
    for relative in entries:
        source = ROOT / relative
        snapshot = CHECKER / relative
        if not source.is_file():
            failures.append(f"monorepo source missing: {relative}")
        elif not snapshot.is_file():
            failures.append(f"checker snapshot missing: {relative}")
        elif digest(source) != digest(snapshot):
            failures.append(f"checker snapshot differs: {relative}")
    if failures:
        print("\n".join(f"ERROR {failure}" for failure in failures), file=sys.stderr)
        return 1
    print(f"PASS checker snapshot matches {len(entries)} monorepo source module(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
