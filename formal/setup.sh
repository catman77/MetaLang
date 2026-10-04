#!/usr/bin/env bash
# Reuse an already-built Mathlib instead of downloading and rebuilding it.
# This is the mandatory first step in a fresh checkout: without it `lake build`
# will try to compile Mathlib from scratch (hours).
set -euo pipefail
SRC="${1:-/home/catman/CatmanCode/SymStructures-RH/.lake/packages}"
cd "$(dirname "$0")"
if [ ! -d "$SRC" ]; then
  echo "No built Mathlib found at: $SRC" >&2
  echo "Either pass the path as an argument, or build the usual way:" >&2
  echo "  lake update && lake exe cache get && lake build" >&2
  exit 1
fi
mkdir -p .lake/packages
for p in "$SRC"/*; do
  ln -sfn "$p" ".lake/packages/$(basename "$p")"
done
echo "Packages linked from $SRC"
ls .lake/packages
