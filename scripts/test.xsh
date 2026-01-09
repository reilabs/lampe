$RAISE_SUBPROC_ERROR = True

import argparse
from pathlib import Path
import os
import re
import shutil
import subprocess
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

def read_lampe_generated_comment():
    mod_path = project_root / "src" / "file_generator" / "mod.rs"
    contents = mod_path.read_text()
    match = re.search(r'LAMPE_GENERATED_COMMENT: &str = "([^"]+)"', contents)
    if not match:
        raise Exception(f"Unable to find LAMPE_GENERATED_COMMENT in {mod_path}")
    return match.group(1)

LAMPE_GENERATED_COMMENT = read_lampe_generated_comment()

def in_ci():
    return "CI" in os.environ

def cleanup_ci_dir(path):
    if not in_ci():
        return
    if os.environ.get("LAMPE_CLEAN_CI_ARTIFACTS") != "1":
        return
    if path.exists():
        shutil.rmtree(path)

def cleanup_ci_lake_build(lampe_dir):
    cleanup_ci_dir(lampe_dir / ".lake" / "build")

def cleanup_ci_artifacts():
    cleanup_ci_dir(project_root / "target")
    if os.environ.get("LAMPE_KEEP_LAKE_CACHE") != "1":
        cleanup_ci_dir(project_root / "Lampe" / ".lake" / "build")
        cleanup_ci_dir(project_root / "stdlib" / "lampe" / ".lake" / "build")
        packages_root_env = os.environ.get("LAKE_PKG_DIR")
        if packages_root_env:
            cleanup_ci_dir(Path(packages_root_env))
        cleanup_ci_dir(project_root / ".lake" / "packages")

def parse_args():
    parser = argparse.ArgumentParser(description='Run Lampe tests')
    parser.add_argument('-t', '--test', dest='test', help='Name of directory with test to run')
    parser.add_argument(
        '-u',
        '--update',
        action='store_true',
        help='Update checked-in files using the new extraction instead of comparing with them',
    )
    return parser.parse_args()

def ensure_cli():
    cli = project_root / "target" / "release" / "lampe"
    if cli.exists():
        return cli
    if in_ci():
        raise Exception("Lampe CLI missing in CI; expected target/release/lampe from artifacts.")
    cd @(project_root)
    cargo build --release
    return cli

def copy_tree(src_dir, dest_dir, skip_names):
    for item in src_dir.iterdir():
        if item.name in skip_names:
            continue
        target = dest_dir / item.name
        if item.is_dir():
            shutil.copytree(item, target)
        else:
            shutil.copy2(item, target)

def copy_test_case(src_dir, dest_dir):
    dest_dir.mkdir(parents=True, exist_ok=True)
    copy_tree(src_dir, dest_dir, {"lampe", "target"})

    lampe_src = src_dir / "lampe"
    if not lampe_src.exists():
        return

    lampe_dest = dest_dir / "lampe"
    lampe_dest.mkdir()
    copy_tree(lampe_src, lampe_dest, {".lake", "lake-manifest.json"})

def run_tests(dir):
    args = parse_args()
    script_dir = project_root / dir
    test_cases_dir = script_dir

    selected_test = args.test or ""
    update_mode = args.update
    if 'LAMPE_TEST_CURRENT_COMMIT_SHA' not in ${...}:
        $LAMPE_TEST_CURRENT_COMMIT_SHA=$(git rev-parse HEAD)

    ensure_cli()

    if selected_test == "":
        test_cases = []
        for item in test_cases_dir.iterdir():
            if item.is_dir() and not item.name.startswith('.') and item != test_cases_dir:
                test_cases.append(item)
    else:
        test_cases = [test_cases_dir / selected_test]

    for test_case in test_cases:
        run_test(test_case, update_mode)
    cleanup_ci_artifacts()

def find_lampe_dirs(dir_path):
    lampe_dirs = []
    root_lampe = dir_path / "lampe"
    if root_lampe.is_dir():
        lampe_dirs.append(root_lampe)
    for item in dir_path.iterdir():
        if item.is_dir():
            lampe_dir = item / "lampe"
            if lampe_dir.is_dir():
                lampe_dirs.append(lampe_dir)
    return sorted(lampe_dirs)

def find_extracted_indexes(lampe_dir):
    indexes = []
    for item in lampe_dir.iterdir():
        if item.is_dir() and item.name != ".lake":
            extracted_index = item / "Extracted.lean"
            if extracted_index.exists():
                indexes.append((item, extracted_index))
    return indexes

def parse_package_namespace(lines, extracted_index):
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("namespace "):
            return stripped[len("namespace "):].strip()
    raise Exception(f"No namespace found in {extracted_index}")

def parse_imports(lines):
    imports = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.append(stripped[len("import "):].strip())
    return imports

def assert_extracted_files_marked_as_generated(lampe_dir):
    indexes = find_extracted_indexes(lampe_dir)
    if not indexes:
        raise Exception(f"No Extracted.lean files found under {lampe_dir}")

    for package_dir, extracted_index in indexes:
        lines = extracted_index.read_text().splitlines()
        namespace = parse_package_namespace(lines, extracted_index)
        imports = parse_imports(lines)
        prefix = f"{namespace}.Extracted."

        if LAMPE_GENERATED_COMMENT not in extracted_index.read_text():
            raise Exception(f"Missing generated header in {extracted_index}")

        for module in imports:
            if not module.startswith(prefix):
                continue
            rel_module = module[len(prefix):]
            if not rel_module:
                continue
            expected_path = package_dir / "Extracted" / Path(*rel_module.split(".")).with_suffix(".lean")
            if not expected_path.exists():
                raise Exception(f"Expected extracted file missing: {expected_path}")
            contents = expected_path.read_text()
            if LAMPE_GENERATED_COMMENT not in contents:
                raise Exception(f"Missing generated header in {expected_path}")

def assert_extraction_matches(working_dir, original_dir):
    diff_cmd = [
        "diff",
        "-r",
        "--exclude=target",
        "--exclude=.lake",
        "--exclude=lake-manifest.json",
        "--exclude=lakefile.toml",
        str(working_dir),
        str(original_dir),
    ]
    subprocess.run(diff_cmd, check=True)

def build_lake(lampe_dir):
    env = os.environ.copy()
    if "CI" in env:
        env.pop("CI", None)
        subprocess.run(["lake", "exe", "cache", "get"], check=True, cwd=lampe_dir, env=env)

    subprocess.run(["lake", "build"], check=True, cwd=lampe_dir, env=env)

def run_test_in_dir(working_dir, original_dir, update_mode):
    cd @(working_dir)
    dir_name = original_dir.name

    cli = ensure_cli()

    print("-" * 40)
    print(f"Running tests in {dir_name}...")
    print("-" * 40)

    if dir_name.startswith('_'):
        return

    if (working_dir / "clean.xsh").exists():
        /usr/bin/env xonsh @(working_dir / "clean.xsh") @(project_root)
    elif (working_dir / "clean.sh").exists():
        /usr/bin/env bash @(working_dir / "clean.sh")

    cmd = [str(cli), "--root", str(working_dir)]
    subprocess.run(cmd, check=True)

    if (working_dir / "user_actions.xsh").exists():
        /usr/bin/env xonsh @(working_dir / "user_actions.xsh") @(project_root)
    elif (working_dir / "user_actions.sh").exists():
        /usr/bin/env bash @(working_dir / "user_actions.sh")

    if not update_mode:
        assert_extraction_matches(working_dir, original_dir)

    lampe_dirs = find_lampe_dirs(working_dir)
    if not lampe_dirs:
        raise Exception(f"No lampe/ directories found under {working_dir}")

    for lampe_dir in lampe_dirs:
        assert_extracted_files_marked_as_generated(lampe_dir)

        lakefile_path = lampe_dir / "lakefile.toml"
        if lakefile_path.exists():
            lampe_path = os.path.relpath(project_root / "Lampe", lampe_dir)
            stdlib_path = os.path.relpath(project_root / "stdlib" / "lampe", lampe_dir)
            change_toml_required_dep_to_path_by_regex(lakefile_path, '^Lampe$', lampe_path)
            change_toml_required_dep_to_path_by_regex(lakefile_path, '^std-.*$', stdlib_path)
            packages_root_env = os.environ.get("LAKE_PKG_DIR")
            if packages_root_env:
                packages_root = Path(packages_root_env)
            else:
                packages_root = project_root / ".lake" / "packages"
            packages_root.mkdir(parents=True, exist_ok=True)
            packages_dir = os.path.relpath(packages_root, lampe_dir)
            set_toml_packages_dir(lakefile_path, packages_dir)
            lake_dir = lampe_dir / ".lake"
            lake_dir.mkdir(parents=True, exist_ok=True)
            packages_link = lake_dir / "packages"
            if packages_link.is_symlink():
                packages_link.unlink()
            if not packages_link.exists():
                packages_link.symlink_to(
                    os.path.relpath(packages_root, lake_dir),
                    target_is_directory=True,
                )
            manifest_path = lampe_dir / "lake-manifest.json"
            if manifest_path.exists():
                set_manifest_packages_dir(manifest_path, packages_dir)

            rev = $LAMPE_TEST_CURRENT_COMMIT_SHA
            change_toml_required_dep_to_rev_by_regex(lakefile_path, '^GitDepWithLampe-.*$', rev)

        build_lake(lampe_dir)
        cleanup_ci_lake_build(lampe_dir)

def run_test(dir_path, update_mode):
    if update_mode:
        run_test_in_dir(dir_path, dir_path, update_mode)
        return

    with tempfile.TemporaryDirectory() as tmp_dir:
        working_dir = Path(tmp_dir)
        copy_test_case(dir_path, working_dir)
        run_test_in_dir(working_dir, dir_path, update_mode)
