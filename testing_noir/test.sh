#!/usr/bin/env bash
set -e

usage(){
>&2 cat << EOF
Usage: $0
   [ -t | --test  ] Name of directory (full path, ex. '/home/user/noir/noir_test_success/should_fail_with_matches') with test to run
   [ --noir-path  ] Path to noir repository
   [ --lampe-cmd  ] Lampe command (default: lampe)
   [ --lake-cmd   ] Lake command (default: lake)
   [ --log-dir    ] Path where to put logs (default: current directory)
   [ --log-stdout ] Define if logs should go to file or stdout - pass true (default: false)
EOF
exit 1
}

while :
do
	if [[ $# -eq 0 ]]; then
		break
	fi
  case $1 in
    -t | --test)          PARAM_TEST=$2          ; shift 2 ;;
    --noir-path)          PARAM_NOIR_PATH=$2     ; shift 2 ;;
    --lampe-cmd)          PARAM_LAMPE_CMD=$2     ; shift 2 ;;
    --lake-cmd)           PARAM_LAKE_CMD=$2      ; shift 2 ;;
    --log-dir)            PARAM_LOG_DIR=$2       ; shift 2 ;;
    --log-stdout)         PARAM_LOG_STDOUT=$2    ; shift 2 ;;
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

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
SELECTED_TEST="${PARAM_TEST:-}"
LAMPE_CMD="${PARAM_LAMPE_CMD:-lampe}"
LAKE_CMD="${PARAM_LAKE_CMD:-lake}"
LOG_DIR="${PARAM_LOG_DIR:-${SCRIPT_DIR}}"
LOG_STDOUT="${PARAM_LOG_STDOUT:-false}"
LOG_FILE="${LOG_DIR}/running.log"
LAKE_DIR="${SCRIPT_DIR}/.lake"

if [ ! -d ${LAKE_DIR} ]; then
	mkdir -p "${LAKE_DIR}"
fi

if [[ "$SELECTED_TEST" == "" ]]; then
	readarray -t test_dirs_1 < <(find "$TEST_PROGRAMS_PATH/compile_success_contract" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
	readarray -t test_dirs_2 < <(find "$TEST_PROGRAMS_PATH/compile_success_empty" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
	readarray -t test_dirs_3 < <(find "$TEST_PROGRAMS_PATH/compile_success_no_bug" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
	readarray -t test_dirs_4 < <(find "$TEST_PROGRAMS_PATH/compile_success_with_bug" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
	readarray -t test_dirs_5 < <(find "$TEST_PROGRAMS_PATH/execution_success" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
	readarray -t test_dirs_6 < <(find "$TEST_PROGRAMS_PATH/noir_test_success" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')
	readarray -t test_dirs_7 < <(find "$TEST_PROGRAMS_PATH/test_libraries" -mindepth 1 -maxdepth 1 -type d -not -path '*/\.*')

	test_dirs=( "${test_dirs_1[@]}" "${test_dirs_2[@]}" "${test_dirs_3[@]}" "${test_dirs_4[@]}" "${test_dirs_5[@]}" "${test_dirs_6[@]}" "${test_dirs_7[@]}" )

	if [ ${#test_dirs[@]} -eq 0 ]; then
		echo "No tests to run. Was looking into ${TEST_PROGRAMS_PATH}".
		exit 1
	fi
else
	test_dirs=( "$SELECTED_TEST" )
fi

# This call logs info with prefix '[0xa1c]'. This is just a random value
# used to make it easier to grep for its output instead of other (lake,
# lampe, etc) programs being run inside.
do_process_test() {
    local dir=$1
    local lake_dir=$2
    local log_file=$3
    local lampe_cmd=$4
    local lake_cmd="$5"
    local dirname=$(basename "$dir")

		echo "[0xa1c] Processing $dir"
		cd $dir

		if ! ${lampe_cmd}; then
			echo "[0xa1c] failed $dir"
			return 0
		fi

		cd lampe

		if [ ! -d .lake ]; then
			ln -s ${lake_dir} .lake
		fi
		if ! ${lake_cmd} exe cache get; then
			echo "[0xa1c] failed $dir"
			return 0
		fi
		if ! ${lake_cmd} build; then
			echo "[0xa1c] failed $dir "
			return 0
		fi

		echo "[0xa1c] succeeded $dir "
}

process_test() {
    local log_file=$3

		if [ "${LOG_STDOUT}" == "true" ]; then
			do_process_test "$@" 2>&1 | tee -a "$log_file"
    else
			do_process_test "$@" 2>&1 >> "$log_file"
    fi
}

rm -f "$LOG_FILE"
num_test_cases=${#test_dirs[@]}
for (( i=0; i<$num_test_cases; i++ )); do
	echo "$(( i + 1))/$num_test_cases"
	process_test "${test_dirs[$i]}" "${LAKE_DIR}" "${LOG_FILE}" "${LAMPE_CMD}" "${LAKE_CMD}"
done

if [ -f "$LOG_FILE" ]; then
		# '[0xa1c]' is a prefix used by output of running test by this script
    failed_dirs=($(grep -a '\[0xa1c\] failed' "$LOG_FILE" | awk '{print $3}'))
    succeeded_dirs=($(grep -a '\[0xa1c\] succeeded' "$LOG_FILE" | awk '{print $3}'))
else
    echo "$LOG_FILE not found or empty. Check for errors." >&2
    exit 1
fi

ESCAPED_TEST_PROGRAMS_PATH="$(echo ${TEST_PROGRAMS_PATH} | sed -e 's/\//\\\//g')"

unexpected_fails=()
for test_dir in "${failed_dirs[@]}"; do
	found=$(cat ${SCRIPT_DIR}/should_fail | sed -e "s/^/${ESCAPED_TEST_PROGRAMS_PATH}\//" | grep $test_dir | wc -l)
	if [ ${found} -eq 0 ]; then
		echo "Test ${test_dir} failed but was not expected to do so"
		unexpected_fails+=("${test_dir}")
	else
		echo "Test ${test_dir} - failed as expected"
	fi
done

unexpected_succeeds=()
for test_dir in "${succeeded_dirs[@]}"; do
	found=$(cat ${SCRIPT_DIR}/should_succeed | sed -e "s/^/${ESCAPED_TEST_PROGRAMS_PATH}\//" | grep $test_dir | wc -l)
	if [ ${found} -eq 0 ]; then
		echo "Test ${test_dir} - succeeded but was not expected to do so"
		unexpected_succeeds+=("${test_dir}")
	else
		echo "Test ${test_dir} - succeeded as expected"
	fi
done

count_expected_mismatch=$(( ${#unexpected_fails[@]} + ${#unexpected_succeeds[@]} ))
if [ ${count_expected_mismatch} -ne 0 ]; then
    echo "Unexpected results (${count_expected_mismatch}/${num_test_cases}) for the run. Fail."
    echo "Unexpected fails:"
    for test_dir in "${unexpected_fails[@]}"; do
    	echo "- ${test_dir}"
    done
    echo "Unexpected succeeds:"
    for test_dir in "${unexpected_succeeds[@]}"; do
    	echo "- ${test_dir}"
    done
    echo "Check ${LOG_FILE} for details."
    exit 1
else
    echo "All run as expected! Success!"
fi
