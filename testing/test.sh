#!/bin/sh
set -e

ORIGINAL_DIR=$(pwd)

PROJECT_ROOT=$(dirname "$(dirname "$(readlink -f "$0")")")

LEAN_ROOT=$PROJECT_ROOT/Lampe/

TEST_PATH=testing/test_fixture

INPUT_FILE=src/main.nr

OUTPUT_FILE=$TEST_PATH/src/Main.lean
EXPECT_FILE=$OUTPUT_FILE.expected

cd $PROJECT_ROOT

echo "Building CLI tool..."
cargo build

echo "Extracting test file..."
cargo run -- --root $TEST_PATH --file $INPUT_FILE --out-file $OUTPUT_FILE

cd $LEAN_ROOT

echo "Building Lean tool..."
lake exe cache get
lake build

echo "Comparing output files..."
sum1=$(sha1sum $PROJECT_ROOT/$OUTPUT_FILE)
sum2=$(sha1sum $PROJECT_ROOT/$EXPECT_FILE)

if [ "$sum1" != "$sum2" ]; then
	echo "Output file does not match the expected"
	exit 1
fi

echo "Parsing output file..."
lake env lean $PROJECT_ROOT/$OUTPUT_FILE

echo "All tests passed!"
cd $ORIGINAL_DIR
