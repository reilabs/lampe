#!/usr/bin/env xonsh

from pathlib import Path

def get_project_root():
    script_dir = Path($(echo $XONSH_SOURCE).strip()).resolve()
    root_dir = script_dir
    while True:
        if (root_dir / '.git').is_dir():
            return root_dir

        if root_dir.resolve() == Path('/'):
            raise Exception("Could not find .git directory in file tree")

        root_dir = root_dir.parent

print('Project root: ' + str(get_project_root()))

source @(get_project_root() / 'scripts' / 'utils.xsh')
source @(get_project_root() / 'scripts' / 'test.xsh')

def main():
    run_tests('examples')

if __name__ == "__main__":
    main()
