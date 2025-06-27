#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

from pathlib import Path
import tempfile

def get_project_root():
    script_dir = Path($(echo $XONSH_SOURCE).strip()).resolve()
    return script_dir.parent.parent

source @(get_project_root() / 'scripts' / 'utils.xsh')

noir_version = read_noir_version()
print('Noir version: ' + noir_version)

with tempfile.TemporaryDirectory() as tmpdirname:
    download_noir_stdlib_to_dir(noir_version, tmpdirname)
    
    stdlib_path = Path(tmpdirname) / 'noir' / 'noir_stdlib'
    project_stdlib_path = get_project_root() / 'stdlib'
    
    cp -R @(str(stdlib_path) + '/.') @(project_stdlib_path)