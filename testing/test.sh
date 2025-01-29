#!/usr/bin/bash
set -euxo pipefail

ORIGINAL_DIR=$(pwd)

PROJECT_ROOT=$(dirname "$(dirname "$(readlink -f "$0")")")

LEAN_ROOT=$PROJECT_ROOT/Lampe/

TEST_PATH=$PROJECT_ROOT/testing/test_fixture

INPUT_FILE=$TEST_PATH/src/main.nr
OUTPUT_FILE=$TEST_PATH/src/Out.lean
OUTPUT_OLEAN=${OUTPUT_FILE%.lean}.olean
EXPECT_FILE=$OUTPUT_FILE.expected
PROOF_FILE=$TEST_PATH/src/Spec.lean

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
sum1=$(sha1sum $OUTPUT_FILE | cut -d' ' -f1)
sum2=$(sha1sum $EXPECT_FILE | cut -d' ' -f1)

if [ "$sum1" != "$sum2" ]; then
	echo $sum1
	echo $sum2
	echo "Output file does not match the expected"
	exit 1
fi

# Set the environment variables
export LEAN_PATH=$(lake env | grep LEAN_PATH | cut -d= -f2 | tr ':' '\n' | xargs realpath | tr '\n' ':')

cd $TEST_PATH/src

echo "Parsing output file..."
lean $OUTPUT_FILE -o $OUTPUT_OLEAN

echo "Checking proofs..."
export LEAN_PATH=$LEAN_PATH:$TEST_PATH"/src/"
lean $PROOF_FILE

echo "All tests passed!"

rm $OUTPUT_FILE
rm $OUTPUT_OLEAN

cd $ORIGINAL_DIR
