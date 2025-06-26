#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

import argparse
import sys
from pathlib import Path

def get_script_dir():
    script_path = Path($(echo $XONSH_SOURCE).strip()).resolve()
    return script_path.parent

def get_project_root(script_dir):
    return script_dir.parent

def parse_args():
    parser = argparse.ArgumentParser(description='Run Lampe tests')
    parser.add_argument('-t', '--test', dest='test', help='Name of directory with test to run')
    parser.add_argument('-u', '--update', action='store_true', help='Update checked-in files using the new extraction instead of comparing with them')
    return parser.parse_args()

def main():
    args = parse_args()
    script_dir = get_script_dir()
    examples_dir = script_dir
    project_root = get_project_root(examples_dir)

    selected_test = args.test or ""
    update_mode = args.update
    lake_dir = examples_dir / ".lake"

    if not lake_dir.exists():
        lake_dir.mkdir()

    cd @(project_root)
    cargo build --release

    cli = project_root / "target" / "release" / "lampe"

    if selected_test == "":
        example_dirs = []
        for item in examples_dir.iterdir():
            if item.is_dir() and not item.name.startswith('.') and item != examples_dir:
                example_dirs.append(item)
    else:
        example_dirs = [examples_dir / selected_test]

    for dir_path in example_dirs:
        cd @(dir_path)
        dir_name = dir_path.name

        if dir_name.startswith('_'):
            continue

        clean_script = dir_path / "clean.sh"
        if clean_script.exists():
            /usr/bin/env bash @(clean_script)

        # Get the extracted dir (if it exists)
        extracted_dirs = list(dir_path.rglob("Extracted"))
        # filter out directories in the `.lake/...` relative path
        extracted_dirs = [d for d in dir_path.rglob("Extracted") if d.is_dir() and not any(part.startswith('.') for part in d.relative_to(dir_path).parts)]

        if not extracted_dirs:
            $(@(cli))
        else:
            extracted_dir = extracted_dirs[0]

            if update_mode:
                # Update mode: run CLI and update checked-in files
                $(@(cli))
            else:
                # Normal mode: compare files
                # rename checked out lean filies
                for lean_file in extracted_dir.rglob("*.lean"):
                    checkedout_file = lean_file.with_suffix(".lean_checkedout")
                    cp @(lean_file) @(checkedout_file)

                # run the CLI
                $(@(cli))

                # check if the extracted files have changed
                for checkedout_file in extracted_dir.rglob("*.lean_checkedout"):
                    generated_file = checkedout_file.with_suffix(".lean")

                    if generated_file.exists():
                        diff_result = $(diff -q @(checkedout_file) @(generated_file)).strip()
                        if diff_result:
                            print(f"MISMATCH: {generated_file} differs from checked-out version")
                            sys.exit(1)
                    else:
                        print(f"MISSING: {generated_file} was not generated")
                        sys.exit(1)

                # check for newly generated files not in checked-out version
                for generated_file in extracted_dir.rglob("*.lean"):
                    checkedout_file = generated_file.with_suffix(".lean_checkedout")
                    if not checkedout_file.exists():
                        print(f"NEW FILE: {generated_file} is newly generated")
                        sys.exit(1)

                # delete renamed files
                for checkedout_file in extracted_dir.rglob("*.lean_checkedout"):
                    checkedout_file.unlink()

        # Overwrite Lampe to local path
        lakefile_path = dir_path / "lampe" / "lakefile.toml"
        if lakefile_path.exists():
            content = lakefile_path.read_text()
            lines = content.split('\n')

            lampe_line_start = -1
            for i, line in enumerate(lines):
                if 'name = "Lampe"' in line:
                    lampe_line_start = i
                    break

            if lampe_line_start > -1:
                lines[lampe_line_start + 1] = 'path = "../../../Lampe"'
                lines[lampe_line_start + 2] = ''
                lines[lampe_line_start + 3] = ''

                lakefile_path.write_text('\n'.join(lines))

        user_actions_script = dir_path / "user_actions.sh"
        if user_actions_script.exists():
            /usr/bin/env bash @(user_actions_script)

        if not update_mode:
            lampe_dir = dir_path / "lampe"
            cd @(lampe_dir)

            lake_symlink = lampe_dir / ".lake"
            if not lake_symlink.exists():
                ln -s @(lake_dir) .lake

            lake exe cache get
            lake build

if __name__ == "__main__":
    main()
