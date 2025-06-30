#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

import argparse
import sys
from pathlib import Path
import subprocess

def get_script_dir():
    script_path = Path($(echo $XONSH_SOURCE).strip()).resolve()
    return script_path.parent

def parse_args():
    parser = argparse.ArgumentParser(description='Run Noir tests with Lampe')
    parser.add_argument('-t', '--test', dest='test', help='Name of directory (full path, ex. "/home/user/noir/noir_test_success/should_fail_with_matches") with test to run')
    parser.add_argument('--noir-path', dest='noir_path', required=True, help='Path to noir repository')
    parser.add_argument('--lampe-cmd', dest='lampe_cmd', default='lampe', help='Lampe command (default: lampe)')
    parser.add_argument('--lake-cmd', dest='lake_cmd', default='lake', help='Lake command (default: lake)')
    parser.add_argument('--log-dir', dest='log_dir', help='Path where to put logs (default: current directory)')
    parser.add_argument('--log-stdout', dest='log_stdout', action='store_true', help='Define if logs should go to file or stdout - pass true (default: false)')
    return parser.parse_args()

def find_test_directories(test_programs_path):
    """Find all test directories in the noir test_programs folder"""
    test_categories = [
        'compile_success_contract',
        'compile_success_empty',
        'compile_success_no_bug',
        'compile_success_with_bug',
        'execution_success',
        'noir_test_success',
        'test_libraries'
    ]

    test_dirs = []
    for category in test_categories:
        category_path = test_programs_path / category
        if category_path.exists():
            for item in category_path.iterdir():
                if item.is_dir() and not item.name.startswith('.'):
                    test_dirs.append(item)

    return test_dirs

def process_test(test_dir, lake_dir, log_file, lampe_cmd, lake_cmd, log_stdout):
    """Process a single test directory"""
    dirname = test_dir.resolve()

    def log_message(msg):
        print(f"[0xa1c] {msg}")
        if log_file and not log_stdout:
            with open(log_file, 'a') as f:
                f.write(f"[0xa1c] {msg}\n")

    log_message(f"Processing {test_dir}")

    try:
        cd @(dirname)

        try:
            $(@(lampe_cmd))
        except subprocess.CalledProcessError:
            log_message(f"failed {test_dir} - lampe command failed")
            return False

        cd lampe

        lake_symlink = ".lake"
        if not Path(lake_symlink).exists():
            ln -s @(lake_dir) .lake

        try:
            $(@(lake_cmd) exe cache get)
        except subprocess.CalledProcessError:
            log_message(f"failed {test_dir} - lake cache get failed")
            return False

        try:
            $(@(lake_cmd) build)
        except subprocess.CalledProcessError:
            log_message(f"failed {test_dir} - lake build failed")
            return False

        log_message(f"succeeded {test_dir}")
        return True

    except Exception as e:
        log_message(f"failed {test_dir} - {str(e)}")
        return False

def read_expected_results(script_dir):
    """Read the should_fail and should_succeed files"""
    should_fail_file = script_dir / "should_fail"
    should_succeed_file = script_dir / "should_succeed"

    should_fail = set()
    should_succeed = set()

    for line in should_fail_file.read_text().splitlines():
        line = line.strip()
        if line:
            should_fail.add(line)

    for line in should_succeed_file.read_text().splitlines():
        line = line.strip()
        if line:
            should_succeed.add(line)

    return should_fail, should_succeed

def check_results(test_results, test_programs_path, script_dir):
    """Check test results against expected outcomes"""
    should_fail, should_succeed = read_expected_results(script_dir)

    failed_dirs = [test_dir for test_dir, success in test_results if not success]
    succeeded_dirs = [test_dir for test_dir, success in test_results if success]

    unexpected_fails = []
    unexpected_succeeds = []

    for test_dir in failed_dirs:
        relative_path = test_dir.relative_to(test_programs_path)
        if str(relative_path) not in should_fail:
            print(f"Test {test_dir} failed but was not expected to do so")
            unexpected_fails.append(test_dir)
        else:
            print(f"Test {test_dir} - failed as expected")

    for test_dir in succeeded_dirs:
        relative_path = test_dir.relative_to(test_programs_path)
        if str(relative_path) not in should_succeed:
            print(f"Test {test_dir} - succeeded but was not expected to do so")
            unexpected_succeeds.append(test_dir)
        else:
            print(f"Test {test_dir} - succeeded as expected")

    return unexpected_fails, unexpected_succeeds

def resolve_test_path(test_name, test_programs_path):
    """Resolve the full path of a test directory"""
    test_path = Path(test_name)
    if not test_path.is_absolute():
        test_path = test_programs_path / test_path

    if not test_path.exists():
        print(f"Test path {test_path} does not exist.")
        sys.exit(1)

    return test_path.resolve()

def main():
    args = parse_args()
    script_dir = get_script_dir()

    noir_path = Path(args.noir_path)
    test_programs_path = noir_path / "test_programs"

    if not test_programs_path.exists():
        print(f"Path to noir repo is not set properly. Couldn't find dir: {test_programs_path}")
        sys.exit(1)

    log_dir = Path(args.log_dir) if args.log_dir else script_dir
    log_file = log_dir / "running.log" if not args.log_stdout else None

    lake_dir = script_dir / ".lake"
    if not lake_dir.exists():
        lake_dir.mkdir(parents=True)

    if args.test:
        test_dirs = [resolve_test_path(args.test, test_programs_path)]
    else:
        test_dirs = find_test_directories(test_programs_path)
        if not test_dirs:
            print(f"No tests to run. Was looking into {test_programs_path}")
            sys.exit(1)

    if log_file and log_file.exists():
        log_file.unlink()

    test_results = []
    num_test_cases = len(test_dirs)
    lampe_cmd = args.lampe_cmd

    if lampe_cmd == 'lampe':
        pass
    elif not Path(lampe_cmd).is_absolute():
        lampe_cmd_path = Path(lampe_cmd).resolve()
        if lampe_cmd_path.exists():
            lampe_cmd = lampe_cmd_path

    for i, test_dir in enumerate(test_dirs):
        print(f"{i + 1}/{num_test_cases}")
        success = process_test(test_dir, lake_dir, log_file, lampe_cmd, args.lake_cmd, args.log_stdout)
        test_results.append((test_dir, success))

    if not args.test:
        unexpected_fails, unexpected_succeeds = check_results(test_results, test_programs_path, script_dir)

        count_expected_mismatch = len(unexpected_fails) + len(unexpected_succeeds)
        if count_expected_mismatch != 0:
            print(f"Unexpected results ({count_expected_mismatch}/{num_test_cases}) for the run. Fail.")
            print("Unexpected fails:")
            for test_dir in unexpected_fails:
                print(f"- {test_dir}")
            print("Unexpected succeeds:")
            for test_dir in unexpected_succeeds:
                print(f"- {test_dir}")
            if log_file:
                print(f"Check {log_file} for details.")
            sys.exit(1)
        else:
            print("All run as expected! Success!")

if __name__ == "__main__":
    main()
