#!/usr/bin/env xonsh

from pathlib import Path
from tomlkit import dumps
from tomlkit import parse
import json
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

rust_cargo_toml_path = project_root / 'Cargo.toml'
ci_noir_yaml_path = project_root / '.github' / 'workflows' / 'ci-noir.yaml'

def load_toml(path):
    with open(path, mode="r") as f:
        return parse(f.read())

def write_toml(path, toml):
    with open(path, mode="w") as f:
        f.write(dumps(toml))

def load_json(path):
    with open(path, mode="r") as f:
        return json.load(f)

def write_json(path, data):
    with open(path, mode="w") as f:
        json.dump(data, f, indent=1)

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

# The rewrite helpers below only write when they actually change something:
# several CI cache keys hash the rewritten files (lakefile.toml,
# lake-manifest.json), and a byte-changing no-op write (e.g. re-serializing
# a manifest that lake formatted differently) silently changes those keys
# between restore and save.
def change_toml_required_dep_to_path_by_regex(toml_path, name_regex, path):
    lakefile_toml = load_toml(toml_path)
    original = dumps(lakefile_toml)

    change_required_dep_to_path_by_regex(lakefile_toml, name_regex, path)

    if dumps(lakefile_toml) != original:
        write_toml(toml_path, lakefile_toml)

def change_manifest_required_dep_to_path_by_regex(manifest_path, name_regex, path):
    manifest = load_json(manifest_path)
    compiled_name_regex = re.compile(name_regex)
    changed = False

    for package in manifest.get('packages', []):
        if not compiled_name_regex.match(package.get('name', '')):
            continue
        if package.get('type') != 'path':
            continue
        if package.get('dir') != path:
            package['dir'] = path
            changed = True

    if changed:
        write_json(manifest_path, manifest)

def read_noir_version():
    rust_cargo_toml = load_toml(rust_cargo_toml_path)
    return rust_cargo_toml['dependencies']['noirc_driver']['rev']

def download_noir_stdlib_to_dir(noir_version, dir_path):
    cd @(dir_path)
    git clone -n --depth=1 --filter=tree:0 https://github.com/noir-lang/noir
    cd noir
    git sparse-checkout set --no-cone /noir_stdlib
    git checkout @(noir_version)
