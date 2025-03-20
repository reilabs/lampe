#!/usr/bin/bash
set -euxo pipefail

EXAMPLES_DIR=$(dirname $(readlink -f "$0"))
PROJECT_ROOT=$(dirname $EXAMPLES_DIR)

(cd $PROJECT_ROOT && cargo build --release)

CLI=$PROJECT_ROOT"/target/release/cli"

readarray -t example_dirs < <(find "$EXAMPLES_DIR" -maxdepth 1 -type d -not -path '*/\.*' -not -path "$EXAMPLES_DIR")

for dir in "${example_dirs[@]}"; do
	cd $dir

  lib_name=$(grep -A1 "^\[package\]" "Nargo.toml" | grep "name" | sed 's/name = "\(.*\)"/\1/')

	if [[ "$lib_name" =~ Dependencies|LocalDependency ]]; then
	  continue
	fi

	$CLI
	if [[ "$lib_name" =~ Merkle ]]; then
		echo "import Merkle.Field" >> lampe/Merkle/Merkle.lean
		echo "import Merkle.Ref" >> lampe/Merkle/Merkle.lean
		echo "import Merkle.Spec" >> lampe/Merkle/Merkle.lean
	fi

	cd lampe/$lib_name

	lake exe cache get
	lake build
done

