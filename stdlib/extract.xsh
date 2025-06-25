#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

from pathlib import Path

def get_project_root():
	script_dir = Path($(echo $XONSH_SOURCE).strip()).resolve()
	return script_dir.parent.parent

project_root = get_project_root()

(cd @(project_root) && cargo build --release)

lampe_cmd = project_root / 'target' / 'release' / 'lampe'

cd @(project_root / 'stdlib')

$(@(lampe_cmd))
