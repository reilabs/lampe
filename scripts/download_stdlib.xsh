#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

from pathlib import Path
import tempfile

def get_project_root():
    script_dir = Path($(echo $XONSH_SOURCE).strip()).resolve()
    root_dir = script_dir
    while True:
        if (root_dir / '.git').is_dir():
            return root_dir

        if root_dir.resolve() == Path('/'):
            raise Exception("Could not find .git directory in file tree")

        root_dir = root_dir.parent

source @(get_project_root() / 'scripts' / 'utils.xsh')

noir_version = read_noir_version()
print('Noir version: ' + noir_version)

with tempfile.TemporaryDirectory() as tmpdirname:
    download_noir_stdlib_to_dir(noir_version, tmpdirname)
    
    stdlib_path = Path(tmpdirname) / 'noir' / 'noir_stdlib'
    project_stdlib_path = get_project_root() / 'stdlib' / 'noir'
    
    cp -R @(str(stdlib_path) + '/.') @(project_stdlib_path)