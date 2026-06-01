$RAISE_SUBPROC_ERROR = True

import argparse
from pathlib import Path
import os
import re
import shutil
import subprocess

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

source @(project_root / "scripts" / "utils.xsh")

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

def run_tests(dir):
    args = parse_args()
    script_dir = project_root / dir
    test_cases_dir = script_dir

    selected_test = args.test or ""
    update_mode = args.update
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

def _git(args, capture=False):
    # Force `safe.directory` so the call works inside CI containers that
    # mount the checkout as a directory owned by a different user; without
    # it git refuses with "Not a git repository" and falls through into
    # `--no-index` mode.
    cmd = [
        "git",
        "-c", "safe.directory=*",
        "-c", f"safe.directory={project_root}",
    ] + args
    return subprocess.run(
        cmd,
        cwd=project_root,
        check=False,
        capture_output=capture,
        text=capture,
    )

def assert_extraction_matches(test_dir):
    # We now run extraction in-place under the checked-in test directory,
    # so reproducibility is checked by asking git whether the working tree
    # under that directory matches HEAD.
    #
    # Files we deliberately do NOT compare:
    #   - ./.lake/**      -> the lake build output (ignored via .gitignore)
    #   - lakefile.toml   -> the CLI is allowed to regenerate it but the
    #                        path = "..." entries for Lampe/stdlib may be
    #                        formatted slightly differently than what is
    #                        checked in; the old diff also excluded this.
    #   - lake-manifest.json -> lake resolves it at build time from inputRev.
    rel = test_dir.relative_to(project_root)
    pathspecs = [
        str(rel),
        f":(exclude){rel}/**/lakefile.toml",
        f":(exclude){rel}/**/lake-manifest.json",
    ]
    # Diff against HEAD, including any unstaged modifications.
    diff = _git(["diff", "--exit-code", "HEAD", "--"] + pathspecs)
    if diff.returncode != 0:
        raise Exception(
            f"Extraction under {test_dir} differs from the checked-in tree. "
            f"Re-run with --update to refresh the snapshot."
        )
    # Untracked files would not appear in `git diff` output, so also
    # check for files that exist in the working tree but not in git
    # (excluding the same lakefile/manifest paths plus standard ignores).
    untracked = _git(
        ["ls-files", "--others", "--exclude-standard", "--"] + pathspecs,
        capture=True,
    )
    if untracked.returncode == 0 and untracked.stdout.strip():
        raise Exception(
            f"Extraction under {test_dir} produced untracked files:\n"
            f"{untracked.stdout}"
            f"Re-run with --update to refresh the snapshot."
        )

def build_lake(lampe_dir):
    subprocess.run(["lake", "exe", "cache", "get"], check=True, cwd=lampe_dir)
    subprocess.run(["lake", "build"], check=True, cwd=lampe_dir)

def rewrite_lampe_stdlib_deps_to_path(lampe_dir):
    # The lampe CLI still generates `git = "https://github.com/reilabs/lampe", rev = "main"`
    # entries for Lampe and the stdlib (see `default_lean_dependencies` in
    # src/file_generator/lake/mod.rs). For tests inside this repo we want
    # those resolved against the local checkout instead, otherwise lake
    # `lake update`s mathlib + batteries against whatever main currently
    # tracks, defeating the build cache and breaking the build whenever
    # the checked-in toolchain diverges from main.
    #
    # We rewrite both the lakefile and (if present) the manifest in place.
    # The git-diff reproducibility check in `assert_extraction_matches`
    # already excludes lakefile.toml + lake-manifest.json so the rewrite
    # is invisible to that check.
    lakefile_path = lampe_dir / "lakefile.toml"
    if not lakefile_path.exists():
        return
    lampe_path = os.path.relpath(project_root / "Lampe", lampe_dir)
    stdlib_path = os.path.relpath(project_root / "stdlib" / "lampe", lampe_dir)
    change_toml_required_dep_to_path_by_regex(lakefile_path, '^Lampe$', lampe_path)
    change_toml_required_dep_to_path_by_regex(lakefile_path, '^std-.*$', stdlib_path)
    manifest_path = lampe_dir / "lake-manifest.json"
    if manifest_path.exists():
        change_manifest_required_dep_to_path_by_regex(manifest_path, '^Lampe$', lampe_path)
        change_manifest_required_dep_to_path_by_regex(manifest_path, '^«std-.*»$', stdlib_path)

def link_packages_dir(lampe_dir):
    # Point each test's `.lake/packages` at the shared `$LAKE_PKG_DIR`
    # cache so consecutive tests reuse the same mathlib / proven-zk /
    # batteries clones. The lakefile and manifest both spell the dir as
    # `.lake/packages`, so the symlink is enough; no further rewriting
    # is required for the package cache to work.
    packages_root_env = os.environ.get("LAKE_PKG_DIR")
    if not packages_root_env:
        return
    packages_root = Path(packages_root_env)
    packages_root.mkdir(parents=True, exist_ok=True)
    lake_dir = lampe_dir / ".lake"
    lake_dir.mkdir(parents=True, exist_ok=True)
    packages_link = lake_dir / "packages"
    if packages_link.is_symlink() or packages_link.exists():
        if packages_link.is_symlink() or not packages_link.is_dir():
            packages_link.unlink()
        else:
            shutil.rmtree(packages_link)
    packages_link.symlink_to(
        os.path.relpath(packages_root, lake_dir),
        target_is_directory=True,
    )

def run_test(dir_path, update_mode):
    cd @(dir_path)
    dir_name = dir_path.name

    cli = ensure_cli()

    print("-" * 40)
    print(f"Running tests in {dir_name}...")
    print("-" * 40)

    if dir_name.startswith('_'):
        return

    if (dir_path / "clean.xsh").exists():
        /usr/bin/env xonsh @(dir_path / "clean.xsh") @(project_root)
    elif (dir_path / "clean.sh").exists():
        /usr/bin/env bash @(dir_path / "clean.sh")

    cmd = [str(cli), "--root", str(dir_path)]
    subprocess.run(cmd, check=True)

    if (dir_path / "user_actions.xsh").exists():
        /usr/bin/env xonsh @(dir_path / "user_actions.xsh") @(project_root)
    elif (dir_path / "user_actions.sh").exists():
        /usr/bin/env bash @(dir_path / "user_actions.sh")

    if not update_mode:
        assert_extraction_matches(dir_path)

    lampe_dirs = find_lampe_dirs(dir_path)
    if not lampe_dirs:
        raise Exception(f"No lampe/ directories found under {dir_path}")

    for lampe_dir in lampe_dirs:
        assert_extracted_files_marked_as_generated(lampe_dir)
        rewrite_lampe_stdlib_deps_to_path(lampe_dir)
        link_packages_dir(lampe_dir)
        build_lake(lampe_dir)
