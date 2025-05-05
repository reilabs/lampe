#!/usr/bin/bash
set -e

usage(){
>&2 cat << EOF
Usage: $0
   [ --noir-path ] Path to noir repository
   [ --lampe-cmd ] Lampe command (default: lampe)
   [ --lake-cmd  ] Lake command (default: lake)
   [ --log-dir   ] Path where to put logs (default: current directory)
EOF
exit 1
}

while :
do
	if [[ $# -eq 0 ]]; then
		break
	fi
  case $1 in
    --noir-path)          PARAM_NOIR_PATH=$2     ; shift 2 ;;
    --lampe-cmd)          PARAM_LAMPE_CMD=$2     ; shift 2 ;;
    --lake-cmd)           PARAM_LAKE_CMD=$2      ; shift 2 ;;
    --log-dir)            PARAM_LOG_DIR=$2       ; shift 2 ;;
    -h | --help)          usage                  ; shift   ;;
    *) >&2 echo Unsupported option: $1
       usage ;;
  esac
done

NOIR_PATH="${PARAM_NOIR_PATH:-}"
if [[ -z "${NOIR_PATH}" ]]; then
	echo "Path to noir repo is not set."
	exit 1
fi
TEST_PROGRAMS_PATH="${NOIR_PATH}/test_programs"

if [[ ! -d ${TEST_PROGRAMS_PATH} ]]; then
	echo "Path to noir repo is not set properly. Couldn't find dir: ${TEST_PROGRAMS_PATH}"
	exit 1
fi

LAMPE_CMD="${PARAM_LAMPE_CMD:-lampe}"
LAKE_CMD="${PARAM_LAKE_CMD:-lake}"
LOG_DIR="${PARAM_LOG_DIR:-$(pwd)}"
LOG_FILE="${LOG_DIR}/running.log"
LAKE_DIR="$(pwd)/.lake"

if [ ! -d ${LAKE_DIR} ]; then
	mkdir -p "${LAKE_DIR}"
fi

readarray -t test_dirs_1 < <(find "$TEST_PROGRAMS_PATH/compile_success_contract" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
readarray -t test_dirs_2 < <(find "$TEST_PROGRAMS_PATH/compile_success_empty" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
readarray -t test_dirs_3 < <(find "$TEST_PROGRAMS_PATH/compile_success_no_bug" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
readarray -t test_dirs_4 < <(find "$TEST_PROGRAMS_PATH/compile_success_with_bug" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
readarray -t test_dirs_5 < <(find "$TEST_PROGRAMS_PATH/execution_success" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
readarray -t test_dirs_6 < <(find "$TEST_PROGRAMS_PATH/noir_test_success" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
readarray -t test_dirs_7 < <(find "$TEST_PROGRAMS_PATH/test_libraries" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')

test_dirs=( "${test_dirs_1[@]}" "${test_dirs_2[@]}" "${test_dirs_3[@]}" "${test_dirs_4[@]}" "${test_dirs_5[@]}" "${test_dirs_6[@]}" "${test_dirs_7[@]}" )

process_test() {
    local dir=$1
    local lake_dir=$2
    local log_file=$3
    local lampe_cmd=$4
    local lake_cmd="$5"
    local dirname=$(basename "$dir")

    {
        echo "[0xa1c] Processing $dir"
				cd $dir

				if ! ${lampe_cmd}; then
					echo "[0xa1c] failed $dir"
					return 0
				fi

				cd lampe

				ln -s ${lake_dir} .lake
				if ! ${lake_cmd} exe cache get; then
					echo "[0xa1c] failed $dir"
					return 0
				fi
				if ! ${lake_cmd} build; then
					echo "[0xa1c] failed $dir "
					return 0
				fi

        echo "[0xa1c] succeeded $dir "
    } >> "$log_file" 2>&1
}

rm -f "$LOG_FILE"
len=${#test_dirs[@]}
for (( i=0; i<$len; i++ )); do
	echo "$i/$len"
	process_test "${test_dirs[$i]}" "${LAKE_DIR}" "${LOG_FILE}" "${LAMPE_CMD}" "${LAKE_CMD}"
done

if [ -f "$LOG_FILE" ]; then
    failed_dirs=($(grep -a '\[0xa1c\] failed' "$LOG_FILE" | awk '{print $2}'))
else
    echo "$LOG_FILE not found or empty. Check for errors." >&2
    exit 1
fi

if [ ${#failed_dirs[@]} -ne 0 ]; then
    echo "Test failures for the following directories:"
    for dir in "${failed_dirs[@]}"; do
        echo "- $dir"
    done
    echo "Check ${LOG_FILE} for details."
    exit 1
else
    echo "Test succeeded!"
fi
