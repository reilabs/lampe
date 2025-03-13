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

