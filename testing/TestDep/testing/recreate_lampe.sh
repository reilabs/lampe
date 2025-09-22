#!/bin/bash

set -eux

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
LAMPE_BIN="${SCRIPT_DIR}/../../../target/release/lampe"

readarray -t deps_dirs < <(find "${SCRIPT_DIR}" -maxdepth 1 -mindepth 1 -type d | grep "WithLampe")

for dep_dir in "${deps_dirs[@]}"; do
	cd $dep_dir

	if [[ -d ./lampe ]]; then
		rm -rf ./lampe
	fi

	${LAMPE_BIN}

	# Overwrite Lampe to local path
	LAMPE_LAKEFILE_LINE_START=$(cat lampe/lakefile.toml | grep -hn "name = \"Lampe\"" | awk -F ':' '{ print $1 }')
	sed -i -e "$(( ${LAMPE_LAKEFILE_LINE_START} + 1 )) c\\" -e "path = \"../../../../../Lampe\"" lampe/lakefile.toml
	sed -i -e "$(( ${LAMPE_LAKEFILE_LINE_START} + 2 )) c\\" -e "" lampe/lakefile.toml
	sed -i -e "$(( ${LAMPE_LAKEFILE_LINE_START} + 3 )) c\\" -e "" lampe/lakefile.toml

	cd lampe

	# lake exe cache get
	# lake build
done
