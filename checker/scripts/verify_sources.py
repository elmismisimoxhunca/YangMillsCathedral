#!/usr/bin/env python3
"""Verify every checked-in source artifact against its directory manifest."""

from __future__ import annotations

import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / "Sources"
METADATA_NAMES = {"FETCH_TIMESTAMP.txt", "PIN.md", "README.md", "SOURCE.md", "SHA256SUMS.txt"}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def verify_manifest(manifest: Path) -> tuple[list[str], set[Path]]:
    errors: list[str] = []
    declared: set[Path] = set()
    if manifest.is_symlink():
        return [f"{manifest}: checksum manifest must not be a symlink"], declared
    try:
        lines = manifest.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as error:
        return [f"{manifest}: unreadable UTF-8 checksum manifest: {error}"], declared
    base = manifest.parent.resolve()
    entries = 0
    for line_number, raw in enumerate(lines, 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(maxsplit=1)
        if len(parts) != 2 or len(parts[0]) != 64:
            errors.append(f"{manifest}:{line_number}: malformed checksum line")
            continue
        expected, relative_text = parts
        relative_text = relative_text.lstrip("*")
        if any(ord(character) < 32 for character in relative_text):
            errors.append(f"{manifest}:{line_number}: control character in artifact path")
            continue
        relative = Path(relative_text)
        if relative.is_absolute() or ".." in relative.parts:
            errors.append(f"{manifest}:{line_number}: unsafe artifact path {relative}")
            continue
        artifact = base / relative
        cursor = base
        symlink_component = False
        for component in relative.parts:
            cursor /= component
            if cursor.is_symlink():
                errors.append(
                    f"{manifest}:{line_number}: artifact path contains symlink component: {relative}"
                )
                symlink_component = True
                break
        if symlink_component:
            continue
        try:
            resolved = artifact.resolve(strict=True)
        except FileNotFoundError:
            errors.append(f"{manifest}:{line_number}: missing {relative}")
            continue
        except (OSError, RuntimeError, ValueError) as error:
            errors.append(f"{manifest}:{line_number}: invalid artifact path {relative}: {error}")
            continue
        if base != resolved.parent and base not in resolved.parents:
            errors.append(f"{manifest}:{line_number}: artifact escapes source directory: {relative}")
            continue
        if artifact.is_symlink() or not resolved.is_file():
            errors.append(f"{manifest}:{line_number}: artifact must be a regular non-symlink file: {relative}")
            continue
        if resolved in declared:
            errors.append(f"{manifest}:{line_number}: duplicate artifact entry {relative}")
            continue
        declared.add(resolved)
        entries += 1
        try:
            actual = digest(resolved)
        except OSError as error:
            errors.append(f"{manifest}:{line_number}: unable to hash {relative}: {error}")
            continue
        if actual != expected.lower():
            errors.append(
                f"{manifest}:{line_number}: hash mismatch for {relative}: "
                f"expected {expected.lower()}, got {actual}"
            )
    if entries == 0:
        errors.append(f"{manifest}: contains no checksum entries")
    else:
        print(f"PASS {manifest.relative_to(ROOT)} ({entries} artifacts)")
    return errors, declared


def main() -> int:
    if SOURCES.is_symlink() or not SOURCES.is_dir():
        print("ERROR Sources must be a real directory", file=sys.stderr)
        return 1
    manifests = sorted(SOURCES.rglob("SHA256SUMS.txt"))
    if not manifests:
        print("ERROR no source checksum manifests found", file=sys.stderr)
        return 1
    errors: list[str] = []
    declared: set[Path] = set()
    for manifest in manifests:
        manifest_errors, manifest_entries = verify_manifest(manifest)
        errors.extend(manifest_errors)
        overlap = declared & manifest_entries
        errors.extend(f"artifact declared by multiple manifests: {path}" for path in sorted(overlap))
        declared.update(manifest_entries)
    metadata_paths: set[Path] = set()
    for manifest in manifests:
        metadata_paths.update(manifest.parent / name for name in METADATA_NAMES)
    for path in sorted(SOURCES.rglob("*")):
        if path.is_symlink():
            errors.append(f"source tree contains a forbidden symlink: {path.relative_to(ROOT)}")
            continue
        if not path.is_file() or path in metadata_paths:
            continue
        if path.resolve() not in declared:
            errors.append(f"unmanifested source artifact: {path.relative_to(ROOT)}")
    if errors:
        for error in errors:
            print(f"ERROR {error}", file=sys.stderr)
        return 1
    print(f"Verified {len(manifests)} source manifest(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
