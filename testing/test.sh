#!/bin/sh
set -e

ORIGINAL_DIR=$(pwd)

PROJECT_ROOT=$(dirname "$(dirname "$(readlink -f "$0")")")

cd "$PROJECT_ROOT"

echo "Running Rust CLI tool..."
cargo run -- --root testing/test_fixture --file src/main.nr --out-file testing/test_fixture/src/Main.lean

echo "Verifying generated Lean code..."
cd Lampe/
lake build
lake env lean $PROJECT_ROOT/testing/test_fixture/src/Main.lean

echo "All tests passed!"

cd "$ORIGINAL_DIR"
