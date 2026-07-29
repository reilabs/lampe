#!/usr/bin/env bash
set -euxo pipefail

# Only remove generated extraction output; keep custom files under lampe/.
for crate in hasher merkle skyscraper; do
  rm -rf ./"$crate"/lampe/*/Extracted
  rm -f ./"$crate"/lampe/*/Extracted.lean
  rm -rf ./"$crate"/lampe/deps/*/lampe/*/Extracted
  rm -f ./"$crate"/lampe/deps/*/lampe/*/Extracted.lean
done
