#!/usr/bin/bash
set -euxo pipefail

EXAMPLES_DIR=$(dirname $(readlink -f "$0"))
PROJECT_ROOT=$(dirname $EXAMPLES_DIR)

usage(){
>&2 cat << EOF
Usage: $0
   [ -t | --test ] Name of directory with test to run
   [ --ci        ] Flag to indicate that test run in CI (on GitHub we need to clean after each test as we run out of disk space)
EOF
exit 1
}

while :
do
	if [[ $# -eq 0 ]]; then
		break
	fi
  case $1 in
    -t | --test) PARAM_TEST=$2    ; shift 2 ;;
    --ci)        PARAM_CI=true    ; shift   ;;
    -h | --help) usage            ; shift   ;;
    *) >&2 echo Unsupported option: $1
       usage ;;
  esac
done

SELECTED_TEST="${PARAM_TEST:-}"
CI_RUN="${PARAM_CI:-false}"
LAKE_DIR="${EXAMPLES_DIR}/.lake"

if [ ! -d ${LAKE_DIR} ]; then
	mkdir -p "${LAKE_DIR}"
fi

(cd $PROJECT_ROOT && cargo build --release)

CLI=$PROJECT_ROOT"/target/release/lampe"

if [[ "$SELECTED_TEST" == "" ]]; then
	readarray -t example_dirs < <(find "$EXAMPLES_DIR" -maxdepth 1 -type d -not -path '*/\.*' -not -path "$EXAMPLES_DIR")
else
	example_dirs=( "$EXAMPLES_DIR/$SELECTED_TEST" )
fi

for dir in "${example_dirs[@]}"; do
	cd $dir
	dir_name=$(basename $dir)

	if [[ $dir_name =~ ^_.* ]]; then
		continue
	fi

	if [[ -f "$dir/clean.sh" ]]; then
		"$dir/clean.sh"
	fi

	# run the CLI and check that the generated files match the checked out files
	if [[ $dir_name == "MerkleFromScratch" || $dir_name == "TestDep" ]]; then
		$CLI
	else
		# rename checked out lean files
		EXTRACTED_DIR=$(find . -type d -name "Extracted")
		if [[ -n $EXTRACTED_DIR ]]; then
			find $EXTRACTED_DIR -name "*.lean" -exec sh -c 'cp "$1" "${1%.lean}.lean_checkedout"' _ {} \;
		fi

		# run the CLI
		$CLI

		# check if the extracted files have changed
		for checkedout_file in $(find $EXTRACTED_DIR -name "*.lean_checkedout"); do
			generated_file="${checkedout_file%.lean_checkedout}.lean"

			if [[ -f "$generated_file" ]]; then
				if ! diff -q "$checkedout_file" "$generated_file" > /dev/null; then
					echo "MISMATCH: $generated_file differs from checked-out version"
					exit 1
				fi
			else
				echo "MISSING: $generated_file was not generated"
				exit 1
			fi
		done

		# check for newly generated files not in checked-out version
		for generated_file in $(find $EXTRACTED_DIR -name "*.lean"); do
			checkedout_file="${generated_file%.lean}.lean_checkedout"
			if [[ ! -f "$checkedout_file" ]]; then
				echo "NEW FILE: $generated_file is newly generated"
				exit 1
			fi
		done

		# delete renamed files
		find $EXTRACTED_DIR -name "*.lean_checkedout" -delete
	fi

	# Overwrite Lampe to local path
	LAMPE_LAKEFILE_LINE_START=$(cat lampe/lakefile.toml | grep -hn "name = \"Lampe\"" | awk -F ':' '{ print $1 }')
	sed -i -e "$(( ${LAMPE_LAKEFILE_LINE_START} + 1 )) c\\" -e "path = \"../../../Lampe\"" lampe/lakefile.toml
	sed -i -e "$(( ${LAMPE_LAKEFILE_LINE_START} + 2 )) c\\" -e "" lampe/lakefile.toml
	sed -i -e "$(( ${LAMPE_LAKEFILE_LINE_START} + 3 )) c\\" -e "" lampe/lakefile.toml

	if [[ -f "$dir/user_actions.sh" ]]; then
		"$dir/user_actions.sh"
	fi

	cd lampe

	if [[ ! -d .lake ]]; then
	  ln -s ${LAKE_DIR} .lake
	fi

	lake exe cache get
	lake build
done

