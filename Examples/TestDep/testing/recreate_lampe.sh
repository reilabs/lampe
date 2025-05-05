#!/bin/bash

set -eux

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
LAMPE_BIN="${SCRIPT_DIR}/../../../target/release/lampe"

readarray -t deps_dirs < <(find "${SCRIPT_DIR}" -maxdepth 1 -mindepth 1 -type d | grep "WithLampe")

for dep_dir in "${deps_dirs[@]}"; do
	cd $dep_dir

	if [[ -d ./lampe ]]; then
		rm -r ./lampe
	fi
	${LAMPE_BIN}
done
