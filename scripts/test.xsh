$RAISE_SUBPROC_ERROR = True

import argparse
from pathlib import Path
import sys
import tempfile

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

def get_script_dir():
    return project_root / "scripts"

def parse_args():
    parser = argparse.ArgumentParser(description='Run Lampe tests')
    parser.add_argument('-t', '--test', dest='test', help='Name of directory with test to run')
    parser.add_argument('-u', '--update', action='store_true', help='Update checked-in files using the new extraction instead of comparing with them')
    return parser.parse_args()

def run_tests(dir):
    args = parse_args()
    script_dir = project_root / dir
    test_cases_dir = script_dir

    selected_test = args.test or ""
    update_mode = args.update
    lake_dir = test_cases_dir / ".lake"

    if 'LAMPE_TEST_CURRENT_COMMIT_SHA' not in ${...}:
        $LAMPE_TEST_CURRENT_COMMIT_SHA=$(git rev-parse HEAD)

    if not lake_dir.exists():
        lake_dir.mkdir()

    cd @(project_root)
    cargo build --release

    if selected_test == "":
        test_cases = []
        for item in test_cases_dir.iterdir():
            if item.is_dir() and not item.name.startswith('.') and item != test_cases_dir:
                test_cases.append(item)
    else:
        test_cases = [test_cases_dir / selected_test]

    for test_case in test_cases:
        run_test(test_case, update_mode, lake_dir)

def is_workspace_test(dir_path):
    """Check if this is a workspace-style test (no lampe/ at root, but subdirs have Nargo.toml)."""
    if (dir_path / "lampe").is_dir():
        return False
    if (dir_path / "Nargo.toml").is_file():
        return False
    # Check if any subdirectory has a Nargo.toml
    for item in dir_path.iterdir():
        if item.is_dir() and (item / "Nargo.toml").is_file():
            return True
    return False

def get_workspace_crates(dir_path):
    """Get list of subcrates in a workspace that have Nargo.toml files."""
    crates = []
    for item in dir_path.iterdir():
        if item.is_dir() and (item / "Nargo.toml").is_file():
            crates.append(item)
    return crates

def get_workspace_crates_with_lampe(dir_path):
    """Get list of subcrates that have both Nargo.toml and lampe/ directory."""
    crates = []
    for item in dir_path.iterdir():
        if item.is_dir() and (item / "Nargo.toml").is_file() and (item / "lampe").is_dir():
            crates.append(item)
    return crates

def run_test(dir_path, update_mode, lake_dir):
    cd @(dir_path)
    dir_name = dir_path.name

    cli = project_root / "target" / "release" / "lampe"

    print("-" * 40)
    print(f"Running tests in {dir_name}...")
    print("-" * 40)

    if dir_name.startswith('_'):
        return

    # Check if this is a workspace-style test
    if is_workspace_test(dir_path):
        run_workspace_test(dir_path, update_mode, lake_dir, cli)
    else:
        run_single_crate_test(dir_path, update_mode, lake_dir, cli)

def run_single_crate_test(dir_path, update_mode, lake_dir, cli):
    """Run test for a single-crate project (original behavior)."""
    cd @(dir_path)

    with tempfile.TemporaryDirectory() as tmp_dir:
        if update_mode:
            working_dir = dir_path
        else:
            # Copy whole test without files excluded by .gitignore (generated ones)
            for subdir in $(find . -mindepth 1 -maxdepth 1 | grep -v -E -i "^\\./(lampe|target)$").strip().split('\n'):
                cp -R @(dir_path / subdir) @(tmp_dir)

            mkdir @(Path(tmp_dir) / "lampe")

            for subdir in $(find ./lampe -mindepth 1 -maxdepth 1 | grep -v -E -i "^\\./lampe/(.lake|lake-manifest.json)$").strip().split('\n'):
                cp -R @(dir_path / subdir) @(Path(tmp_dir) / "lampe")

            working_dir = Path(tmp_dir)

        cd @(working_dir)

        if (working_dir / "clean.xsh").exists():
            /usr/bin/env xonsh @(working_dir / "clean.xsh") @(project_root)
        elif (working_dir / "clean.sh").exists():
            /usr/bin/env bash @(working_dir / "clean.sh")
        else:
            # No clean script found
            pass

        $(@(cli))

        if (working_dir / "user_actions.xsh").exists():
            /usr/bin/env xonsh @(working_dir / "user_actions.xsh") @(project_root)
        elif (working_dir / "user_actions.sh").exists():
            /usr/bin/env bash @(working_dir / "user_actions.sh")
        else:
            # No user actions script found
            pass

        if not update_mode:
            # This command is not perfect but works.
            diff -r --exclude=target --exclude=.lake --exclude=lake-manifest.json --exclude=lakefile.toml @(working_dir) @(dir_path)

            # Overwrite Lampe to local path
            lakefile_path = working_dir / "lampe" / "lakefile.toml"
            if lakefile_path.exists():
                change_toml_required_dep_to_path_by_regex(lakefile_path, '^Lampe$', Path(project_root / "Lampe").absolute().as_posix())
                change_toml_required_dep_to_path_by_regex(lakefile_path, '^std-.*$', Path(project_root / "stdlib" / "lampe").absolute().as_posix())

                rev = $LAMPE_TEST_CURRENT_COMMIT_SHA
                change_toml_required_dep_to_rev_by_regex(lakefile_path, '^GitDepWithLampe-.*$', rev)

            lampe_dir = working_dir / "lampe"
            cd @(lampe_dir)

            lake_symlink = lampe_dir / ".lake"
            if not lake_symlink.exists():
                ln -s @(lake_dir) .lake

            lake exe cache get
            lake build

def run_workspace_test(dir_path, update_mode, lake_dir, cli):
    """Run test for a workspace-style project with multiple crates."""
    # Only test crates that have a lampe/ directory (indicating they should be tested)
    crates = get_workspace_crates_with_lampe(dir_path)

    with tempfile.TemporaryDirectory() as tmp_dir:
        if update_mode:
            working_dir = dir_path
        else:
            # Copy entire workspace structure, excluding lampe/ and target/ in each crate
            cd @(dir_path)
            for item in dir_path.iterdir():
                if item.name.startswith('.'):
                    # Copy dotfiles
                    cp -R @(item) @(tmp_dir)
                elif item.is_dir():
                    # For directories, copy but exclude lampe/.lake and target/
                    dest = Path(tmp_dir) / item.name
                    mkdir -p @(dest)
                    for subitem in item.iterdir():
                        if subitem.name in ['target']:
                            continue
                        if subitem.name == 'lampe':
                            # Copy lampe/ but exclude .lake and lake-manifest.json
                            lampe_dest = dest / 'lampe'
                            mkdir -p @(lampe_dest)
                            for lampe_item in subitem.iterdir():
                                if lampe_item.name in ['.lake', 'lake-manifest.json']:
                                    continue
                                cp -R @(lampe_item) @(lampe_dest)
                        else:
                            cp -R @(subitem) @(dest)
                else:
                    cp @(item) @(tmp_dir)

            working_dir = Path(tmp_dir)

        # Run clean scripts if present at workspace root
        cd @(working_dir)
        if (working_dir / "clean.xsh").exists():
            /usr/bin/env xonsh @(working_dir / "clean.xsh") @(project_root)
        elif (working_dir / "clean.sh").exists():
            /usr/bin/env bash @(working_dir / "clean.sh")

        # Run lampe CLI for each crate with Nargo.toml
        for crate in crates:
            crate_working = working_dir / crate.name
            cd @(crate_working)
            $(@(cli))

        # Run user actions if present at workspace root
        cd @(working_dir)
        if (working_dir / "user_actions.xsh").exists():
            /usr/bin/env xonsh @(working_dir / "user_actions.xsh") @(project_root)
        elif (working_dir / "user_actions.sh").exists():
            /usr/bin/env bash @(working_dir / "user_actions.sh")

        if not update_mode:
            # Compare entire workspace
            diff -r --exclude=target --exclude=.lake --exclude=lake-manifest.json --exclude=lakefile.toml @(working_dir) @(dir_path)

            # Build each crate that has a lampe/ directory
            for crate in crates:
                crate_working = working_dir / crate.name
                lampe_dir = crate_working / "lampe"

                if not lampe_dir.exists():
                    continue

                # Overwrite Lampe to local path
                lakefile_path = lampe_dir / "lakefile.toml"
                if lakefile_path.exists():
                    change_toml_required_dep_to_path_by_regex(lakefile_path, '^Lampe$', Path(project_root / "Lampe").absolute().as_posix())
                    change_toml_required_dep_to_path_by_regex(lakefile_path, '^std-.*$', Path(project_root / "stdlib" / "lampe").absolute().as_posix())

                    rev = $LAMPE_TEST_CURRENT_COMMIT_SHA
                    change_toml_required_dep_to_rev_by_regex(lakefile_path, '^GitDepWithLampe-.*$', rev)

                cd @(lampe_dir)

                lake_symlink = lampe_dir / ".lake"
                if not lake_symlink.exists():
                    ln -s @(lake_dir) .lake

                lake exe cache get
                lake build
