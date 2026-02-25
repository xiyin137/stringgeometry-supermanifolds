#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

ALLOWLIST="StringGeometry/Supermanifolds/sorry_allowlist.txt"

if [[ ! -f "$ALLOWLIST" ]]; then
  echo "Missing allowlist: $ALLOWLIST" >&2
  exit 1
fi

echo "[1/3] Checking for non-allowlisted sorrys in StringGeometry/Supermanifolds..."
TMP_FILE="$(mktemp)"
trap 'rm -f "$TMP_FILE"' EXIT

if command -v rg >/dev/null 2>&1; then
  rg -n '\bsorry\b' StringGeometry/Supermanifolds --glob '*.lean' > "$TMP_FILE" || true
else
  grep -R -n -w --include='*.lean' 'sorry' StringGeometry/Supermanifolds > "$TMP_FILE" || true
fi

DISALLOWED=""
while IFS= read -r line; do
  [[ -z "$line" ]] && continue
  file="${line%%:*}"
  if ! grep -Fxq "$file" "$ALLOWLIST"; then
    DISALLOWED+="$line"$'\n'
  fi
done < "$TMP_FILE"

if [[ -n "$DISALLOWED" ]]; then
  echo "Found disallowed sorry occurrences:" >&2
  printf '%s' "$DISALLOWED" >&2
  exit 1
fi

echo "[2/3] Targeted module checks..."
lake env lean StringGeometry/Supermanifolds.lean
lake env lean StringGeometry/Supermanifolds/Integration/GlobalStokes.lean

echo "[3/3] Supermanifolds quality gate passed."
