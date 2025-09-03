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

# This is a hack for xonsh. This way we have global value
# initialized only once across all runs. It is required for some
# scripts that are being imported with source command and being
# run from directory outside of the project tree (like copied).
try:
    try_get_project_root = project_root
except NameError:
    project_root = get_project_root()
# --- End of copied part.

(cd @(project_root) && cargo build --release)

lampe_cmd = project_root / 'target' / 'release' / 'lampe'

cd @(project_root / 'stdlib')

$(@(lampe_cmd) --root "./" --target "./")
