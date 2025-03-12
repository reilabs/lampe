#!/usr/bin/bash
set -euxo pipefail

EXAMPLES_DIR=$(dirname $(readlink -f "$0"))
PROJECT_ROOT=$(dirname $EXAMPLES_DIR)

(cd $PROJECT_ROOT && cargo build --release)

CLI=$PROJECT_ROOT"/target/release/cli"

readarray -t example_dirs < <(find "$EXAMPLES_DIR" -maxdepth 1 -type d -not -path '*/\.*' -not -path "$EXAMPLES_DIR")

for dir in "${example_dirs[@]}"; do
	cd $dir

	lib_name=$(grep -A1 "^\[\[lean_lib\]\]" "lakefile.toml" | grep "name" | sed 's/name = "\(.*\)"/\1/')
	extracted=$lib_name/"Extracted.lean"
	extracted_temp=$extracted".temp"
	mv $extracted $extracted_temp

	$CLI --root $dir"/src" --out-file $extracted

	lake exe cache get
	lake build

	rm $extracted
	mv $extracted_temp $extracted
done

# LEAN_ROOT=$PROJECT_ROOT/Lampe/
#
# TEST_PATH=$PROJECT_ROOT/testing/test_fixture
#
# INPUT_FILE=$TEST_PATH/src/main.nr
# OUTPUT_FILE=$TEST_PATH/src/Out.lean
# OUTPUT_OLEAN=${OUTPUT_FILE%.lean}.olean
# EXPECT_FILE=$OUTPUT_FILE.expected
# PROOF_FILE=$TEST_PATH/src/Spec.lean
#
# cd $PROJECT_ROOT
#
# echo "Building CLI tool..."
# cargo build
#
# echo "Extracting test file..."
# cargo run -- --root $TEST_PATH --file $INPUT_FILE --out-file $OUTPUT_FILE
#
# cd $LEAN_ROOT
#
# echo "Building Lean tool..."
# lake exe cache get
# lake build
#
# echo "Comparing output files..."
# sum1=$(sha1sum $OUTPUT_FILE | cut -d' ' -f1)
# sum2=$(sha1sum $EXPECT_FILE | cut -d' ' -f1)
#
# if [ "$sum1" != "$sum2" ]; then
# 	echo $sum1
# 	echo $sum2
# 	echo "Output file does not match the expected"
# 	exit 1
# fi
#
# # Set the environment variables
# export LEAN_PATH=$(lake env | grep LEAN_PATH | cut -d= -f2 | tr ':' '\n' | xargs realpath | tr '\n' ':')
# export LEAN=$(lake env | grep LEAN= | cut -d= -f2)
#
# elan default $(cat lean-toolchain)
#
# cd $TEST_PATH/src
#
# echo "Parsing output file..."
# $LEAN $OUTPUT_FILE -o $OUTPUT_OLEAN
#
# echo "Checking proofs..."
# export LEAN_PATH=$LEAN_PATH:$TEST_PATH"/src/"
# $LEAN $PROOF_FILE
#
# echo "All tests passed!"
#
# unset LEAN_PATH
# unset LEAN
# rm $OUTPUT_FILE
# rm $OUTPUT_OLEAN
#
# cd $ORIGINAL_DIR
