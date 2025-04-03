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

	# Run Lampe generation
	$CLI

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

