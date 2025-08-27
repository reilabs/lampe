#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

from pathlib import Path
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

project_root = get_project_root()
# --- End of copied part.

source @(project_root / 'scripts' / 'utils.xsh')

noir_version = read_noir_version()
print('Noir version: ' + noir_version)

rust_cargo_toml = load_toml(rust_cargo_toml_path)

assert noir_version == rust_cargo_toml['dependencies']['fm']['rev']
assert noir_version == rust_cargo_toml['dependencies']['nargo']['rev']
assert noir_version == rust_cargo_toml['dependencies']['nargo_toml']['rev']
assert noir_version == rust_cargo_toml['dependencies']['noirc_driver']['rev']
assert noir_version == rust_cargo_toml['dependencies']['noirc_errors']['rev']
assert noir_version == rust_cargo_toml['dependencies']['noirc_frontend']['rev']

ci_noir_yaml = load_yaml(ci_noir_yaml_path)

assert 'actions/checkout@v4' == ci_noir_yaml['jobs']['run-tests']['steps'][0]['uses']
assert 'noir-lang/noir' == ci_noir_yaml['jobs']['run-tests']['steps'][0]['with']['repository']
assert noir_version == ci_noir_yaml['jobs']['run-tests']['steps'][0]['with']['ref']
assert 'noir' == ci_noir_yaml['jobs']['run-tests']['steps'][0]['with']['path']

with tempfile.TemporaryDirectory() as tmpdirname:
    download_noir_stdlib_to_dir(noir_version, tmpdirname)

    stdlib_path = Path(tmpdirname) / 'noir' / 'noir_stdlib'
    project_stdlib_path = project_root / 'stdlib' / 'noir'

    diff -x Nargo.toml -r @(stdlib_path) @(project_stdlib_path)
