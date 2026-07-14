#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -gt 1 ]; then
  echo "usage: $0 [path-to-comparator-binary]" >&2
  exit 2
fi

if [ "$(uname -s)" != "Linux" ]; then
  echo "comparator requires landrun, and landrun is Linux-only." >&2
  exit 1
fi

if [ "$#" -eq 1 ]; then
  COMPARATOR_BIN="$1"
elif [ -x ".proof-audit-tools/bin/comparator" ]; then
  COMPARATOR_BIN=".proof-audit-tools/bin/comparator"
else
  COMPARATOR_BIN="comparator"
fi

if [[ "$COMPARATOR_BIN" == */* ]]; then
  COMPARATOR_DIR="$(cd "$(dirname "$COMPARATOR_BIN")" && pwd)"
  export PATH="$COMPARATOR_DIR:$PATH"
fi

CONFIG="Comparator/config.json"

for cmd in "$COMPARATOR_BIN" landrun lean4export lake; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "missing required command: $cmd" >&2
    exit 1
  fi
done

if [ ! -f "$CONFIG" ]; then
  echo "missing comparator config: $CONFIG" >&2
  exit 1
fi

echo "Running comparator with $CONFIG"
lake env "$COMPARATOR_BIN" "$CONFIG"
