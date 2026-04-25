#!/usr/bin/env bash
set -euxo pipefail

# Only remove generated extraction output; keep custom files under lampe/.
rm -rf ./lampe/*/Extracted
rm -f ./lampe/*/Extracted.lean
rm -rf ./lampe/deps/*/lampe/*/Extracted
rm -f ./lampe/deps/*/lampe/*/Extracted.lean
