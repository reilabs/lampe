#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

from pathlib import Path

project_root = Path($ARG1)

source @(project_root / 'scripts' / 'utils.xsh')

cat ./user_files/append_to_TestDep.lean >> ./lampe/TestDep-0.0.0.lean
