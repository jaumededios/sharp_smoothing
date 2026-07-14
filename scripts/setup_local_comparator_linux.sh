#!/usr/bin/env bash
set -euo pipefail

if [ "$(uname -s)" != "Linux" ]; then
  echo "this setup script is for Linux only" >&2
  exit 1
fi

for cmd in git lake go; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "missing required command: $cmd" >&2
    exit 1
  fi
done

ROOT_DIR="$(pwd)"
TOOLS_DIR="${ROOT_DIR}/.proof-audit-tools"
SRC_DIR="${TOOLS_DIR}/src"
BIN_DIR="${TOOLS_DIR}/bin"
COMPARATOR_COMMIT="07bc4ea40f2266dcb861820a2ec1fa3244ed307f"
LANDRUN_COMMIT="5ed4a3db3a4ad930d577215c6b9abaa19df7f99f"

mkdir -p "$SRC_DIR" "$BIN_DIR"

if [ ! -d "$SRC_DIR/comparator/.git" ]; then
  git clone https://github.com/leanprover/comparator.git "$SRC_DIR/comparator"
fi

git -C "$SRC_DIR/comparator" fetch origin "$COMPARATOR_COMMIT"
git -C "$SRC_DIR/comparator" checkout --detach "$COMPARATOR_COMMIT"

(cd "$SRC_DIR/comparator" && lake build comparator lean4export)

cp "$SRC_DIR/comparator/.lake/build/bin/comparator" "$BIN_DIR/comparator"
cp "$SRC_DIR/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" \
  "$BIN_DIR/lean4export"
GOBIN="$BIN_DIR" go install \
  "github.com/zouuup/landrun/cmd/landrun@${LANDRUN_COMMIT}"

echo "Installed comparator toolchain into $BIN_DIR"
echo "Run:"
echo "  ./scripts/run_local_comparator.sh"
