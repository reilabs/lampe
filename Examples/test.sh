#!/usr/bin/bash
set -euxo pipefail

EXAMPLES_DIR=$(dirname $(readlink -f "$0"))
PROJECT_ROOT=$(dirname $EXAMPLES_DIR)

SELECTED_TEST="${1:-}"

(cd $PROJECT_ROOT && cargo build --release)

CLI=$PROJECT_ROOT"/target/release/cli"

if [[ "$SELECTED_TEST" == "" ]]; then
	readarray -t example_dirs < <(find "$EXAMPLES_DIR" -maxdepth 1 -type d -not -path '*/\.*' -not -path "$EXAMPLES_DIR")
else
	example_dirs=( "$EXAMPLES_DIR/$SELECTED_TEST" )
fi

for dir in "${example_dirs[@]}"; do
	cd $dir
	dir_name=$(basename $dir)

  # Tests to skip
	if [[ "$dir_name" =~ Dependencies|LocalDependency ]]; then
	  continue
	fi

	if [[ -f "$dir/clean.sh" ]]; then
		"$dir/clean.sh"
	fi

	# Run Lampe generation
	$CLI

	if [[ -f "$dir/user_actions.sh" ]]; then
		"$dir/user_actions.sh"
	fi

	cd lampe

	lake exe cache get
	lake build
done

