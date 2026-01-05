#!/usr/bin/env xonsh

from pathlib import Path

# --- Start of copied part.
# This method is used to resolve the project's root directory,
# which is necessary for importing dependencies and other files.
# It is copied into every *.xsh file we use.
# If you make changes to this method, be sure to update all other
# copies as well.
def get_project_root():
    script_dir = Path($(echo $XONSH_SOURCE).strip()).resolve()
    root_dir = script_dir
    while True:
        if (root_dir / '.git').is_dir():
            return root_dir

        if root_dir.resolve() == Path('/'):
            raise Exception("Could not find .git directory in file tree")

        root_dir = root_dir.parent

# This is a hack for xonsh. This way we have global value
# initialized only once across all runs. It is required for some
# scripts that are being imported with source command and being
# run from directory outside of the project tree (like copied).
try:
    try_get_project_root = project_root
except NameError:
    project_root = get_project_root()
# --- End of copied part.

source @(project_root / 'scripts' / 'utils.xsh')
source @(project_root / 'scripts' / 'test.xsh')

def main():
    args = parse_args()
    update_mode = args.update

    test_case = project_root / 'stdlib'

    if 'LAMPE_TEST_CURRENT_COMMIT_SHA' not in ${...}:
        $LAMPE_TEST_CURRENT_COMMIT_SHA=$(git rev-parse HEAD)

    run_test(test_case, update_mode)
    cleanup_ci_artifacts()

if __name__ == "__main__":
    main()
