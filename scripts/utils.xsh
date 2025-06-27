#!/usr/bin/env xonsh

from pathlib import Path
from tomlkit import dumps
from tomlkit import parse
import yaml

lakefile_toml_path = get_project_root() / 'testing' / 'MerkleFromScratch' / 'lampe' / 'lakefile.toml'
rust_cargo_toml_path = get_project_root() / 'Cargo.toml'
ci_noir_yaml_path = get_project_root() / '.github' / 'workflows' / 'ci-noir.yaml'

def get_project_root():
    script_dir = Path($(echo $XONSH_SOURCE).strip()).resolve()
    root_dir = script_dir
    while True:
        if (root_dir / '.git').is_dir():
            return root_dir

        if root_dir.resolve() == Path('/'):
            raise Exception("Could not find .git directory in file tree")

        root_dir = root_dir.parent

def load_toml(path):
    with open(path, mode="r") as f:
        return parse(f.read())

def write_toml(path, toml):
    with open(path, mode="w") as f:
        f.write(dumps(toml))

def load_yaml(path):
    with open(path, mode="r") as f:
        return yaml.safe_load(f)

def change_required_lampe_to_path(toml, path):
    for i, v in enumerate(toml['require']):
        if v['name'] != 'Lampe':
                continue

        keys = list(v.keys())
        for key in keys:
            if key == 'name':
                    continue
            del v[key]

        v['path'] = 'fakePath'

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
