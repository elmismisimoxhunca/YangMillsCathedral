#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEGACY="$ROOT/YangMills"
HIDDEN="$ROOT/.checker-independence-hidden-YangMills"

if [[ ! -d "$LEGACY" ]]; then
  echo "ERROR legacy YangMills directory is missing" >&2
  exit 1
fi
if [[ -e "$HIDDEN" ]]; then
  echo "ERROR stale hidden-directory path exists: $HIDDEN" >&2
  exit 1
fi

restore() {
  if [[ -d "$HIDDEN" ]]; then
    mv "$HIDDEN" "$LEGACY"
  fi
}
trap restore EXIT INT TERM

mv "$LEGACY" "$HIDDEN"
cd "$ROOT/checker"
python3 scripts/verify_checker.py
lake build YangMillsChecker

echo "PASS standalone checker builds with the legacy YangMills tree hidden"
