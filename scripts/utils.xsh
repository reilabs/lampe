#!/usr/bin/env xonsh

from pathlib import Path
from tomlkit import dumps
from tomlkit import parse
import yaml
import re

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

lakefile_toml_path = project_root / 'testing' / 'MerkleFromScratch' / 'lampe' / 'lakefile.toml'
rust_cargo_toml_path = project_root / 'Cargo.toml'
ci_noir_yaml_path = project_root / '.github' / 'workflows' / 'ci-noir.yaml'

def load_toml(path):
    with open(path, mode="r") as f:
        return parse(f.read())

def write_toml(path, toml):
    with open(path, mode="w") as f:
        f.write(dumps(toml))

def load_yaml(path):
    with open(path, mode="r") as f:
        return yaml.safe_load(f)

def change_required_dep_to_path_by_regex(toml, name_regex, path):
    compiled_name_regex = re.compile(name_regex)

    for i, v in enumerate(toml['require']):
        if not compiled_name_regex.match(v['name']):
                continue

        keys = list(v.keys())
        for key in keys:
            if key == 'name':
                    continue
            del v[key]

        v['path'] = path

    return toml

def change_required_dep_to_rev_by_regex(toml, name_regex, rev):
    compiled_name_regex = re.compile(name_regex)

    for i, v in enumerate(toml['require']):
        if not compiled_name_regex.match(v['name']):
                continue

        v['rev'] = rev

    return toml

def change_toml_required_dep_to_path_by_regex(toml_path, name_regex, path):
    lakefile_toml = load_toml(toml_path)

    change_required_dep_to_path_by_regex(lakefile_toml, name_regex, path)

    write_toml(toml_path, lakefile_toml)

def change_toml_required_dep_to_rev_by_regex(toml_path, name_regex, rev):
    lakefile_toml = load_toml(toml_path)

    change_required_dep_to_rev_by_regex(lakefile_toml, name_regex, rev)

    write_toml(toml_path, lakefile_toml)

def change_required_lampe_to_path(toml, path):
    for i, v in enumerate(toml['require']):
        if v['name'] != 'Lampe':
                continue

        keys = list(v.keys())
        for key in keys:
            if key == 'name':
                    continue
            del v[key]

        v['path'] = path

    return toml

def change_toml_required_lampe_to_path(toml_path, lampe_path):
    lakefile_toml = load_toml(toml_path)

    change_required_lampe_to_path(lakefile_toml, lampe_path)

    write_toml(toml_path, lakefile_toml)

def read_noir_version():
    rust_cargo_toml = load_toml(rust_cargo_toml_path)
    return rust_cargo_toml['dependencies']['noirc_driver']['rev']

def download_noir_stdlib_to_dir(noir_version, dir_path):
    cd @(dir_path)
    git clone -n --depth=1 --filter=tree:0 https://github.com/noir-lang/noir
    cd noir
    git sparse-checkout set --no-cone /noir_stdlib
    git checkout @(noir_version)
