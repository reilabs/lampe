#!/usr/bin/env bash
#
# Bake Mathlib's olean cache into the CI image.
#
# Why: `lake exe cache get` downloads `leantar` + several GB of olean
# blobs at the start of every CI job. Both downloads have been flaky on
# GitHub-hosted runners (504 from the GitHub release CDN, corrupt tar).
# Baking the cache once per image build means per-job `lake exe cache
# get` becomes a hash-check + decompress with no network access.
#
# Output: $LAMPE_BAKED_MATHLIB_CACHE (default /opt/lampe-cache/mathlib/)
# populated with `leantar` and the unpacked `*.olean.json` files.
# Workflows hydrate `$HOME/.cache/mathlib/` from there before calling
# `lake exe cache get`.

set -euo pipefail

if [[ -z "${MATHLIB_REV:-}" ]]; then
    echo "MATHLIB_REV not set; skipping mathlib cache bake."
    exit 0
fi

if [[ -z "${LEAN_TOOLCHAIN:-}" ]]; then
    echo "LEAN_TOOLCHAIN not set; cannot bake mathlib cache."
    exit 1
fi

OUT_DIR="${LAMPE_BAKED_MATHLIB_CACHE:-/opt/lampe-cache/mathlib}"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

mkdir -p "$OUT_DIR"

# Pretend $HOME points into our work dir so the cache lands in a known
# place we can move to $OUT_DIR. Mathlib's cache tool hardcodes
# `$HOME/.cache/mathlib` as the on-disk cache root.
export HOME="$WORK_DIR/home"
mkdir -p "$HOME/.cache/mathlib"

cd "$WORK_DIR"
mkdir -p MathlibBootstrap

echo "$LEAN_TOOLCHAIN" > lean-toolchain

cat > lakefile.toml <<EOF
name = "mathlib_cache_bootstrap"
defaultTargets = ["MathlibBootstrap"]

[[lean_lib]]
name = "MathlibBootstrap"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "$MATHLIB_REV"
EOF

# Empty top-level so the lib resolves; we never build it.
: > MathlibBootstrap.lean

lake update mathlib
lake exe cache get

# Move the cache to the image-stable path. Use `mv` so the inode count
# stays low and the image layer reflects the cache footprint once.
mv "$HOME/.cache/mathlib"/* "$OUT_DIR/"

echo "Baked mathlib cache to $OUT_DIR:"
du -sh "$OUT_DIR" || true
ls "$OUT_DIR" | head -5 || true
