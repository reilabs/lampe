#!/usr/bin/env bash
# Populates the mathlib `.ltar` store at $MATHLIB_CACHE_DIR from the bake
# workspace at /opt/lake-bake. See the comment block in docker/ci/Dockerfile
# for why the store is baked into the image and how the layout works.
set -euo pipefail

store_ltars() {
  find "${MATHLIB_CACHE_DIR}" -type f -name '*.ltar' | wc -l
}

mkdir -p "${MATHLIB_CACHE_DIR}"
cd /opt/lake-bake

if [ "$(store_ltars)" -lt 1000 ]; then
  lake exe cache get- || true
fi

if [ "$(store_ltars)" -lt 1000 ]; then
  lake exe cache get || true
  lake build mathlib/Mathlib batteries/Batteries
  cd .lake/packages/mathlib
  mkdir -p .lake/packages
  for dep in /opt/lake-bake/.lake/packages/*/; do
    dep=${dep%/}
    if [ "$(basename "$dep")" != mathlib ]; then
      mv "$dep" .lake/packages/
    fi
  done
  lake exe cache pack
  cd /opt/lake-bake
fi

rm -rf /opt/lake-bake/.lake

if [ "$(store_ltars)" -lt 1000 ]; then
  echo "mathlib ltar store is incomplete ($(store_ltars) archives); refusing to ship it"
  exit 1
fi
