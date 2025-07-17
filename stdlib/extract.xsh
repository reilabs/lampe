#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

from pathlib import Path

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

(cd @(project_root) && cargo build --release)

lampe_cmd = project_root / 'target' / 'release' / 'lampe'

cd @(project_root / 'stdlib')

$(@(lampe_cmd) --root "./noir" --target "./lampe")
