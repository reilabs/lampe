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

source @(project_root / 'scripts' / 'utils.xsh')

def change_lampe_dependencies_rev(toml, rev):
    for i, v in enumerate(toml['require']):
        if 'git' not in v || v['git'] != 'https://github.com/reilabs/lampe':
                continue

        v['rev'] = rev

    return toml

def change_toml_required_lampe_to_path(toml_path, rev):
    lakefile_toml = load_toml(toml_path)

    change_lampe_dependencies_rev(lakefile_toml, rev)

    write_toml(toml_path, lakefile_toml)

def make_merkle_import(libname):
    return "import «" + libname + "».Extracted\n"

rev = $(git rev-parse HEAD)
change_toml_required_lampe_to_path('./lampe/lakefile.toml', rev)

with open('./lampe/TestDep-0.0.0.lean', 'r+') as f:
    content = f.readlines()

    for i, line in enumerate(content):
        if line.startswith('import'):
            import_line = i
            break

    content.insert(import_line, make_merkle_import('GitDepWithLampe-0.0.0'))
    content.insert(import_line, make_merkle_import('GitDepWithLampe-1.0.0'))
    content.insert(import_line, make_merkle_import('GitDepWithLampe-2.0.0'))
    content.insert(import_line, make_merkle_import('LocalDepWithLampe-0.0.0'))
    content.insert(import_line, make_merkle_import('LocalDepWithLampe-1.0.0'))
    content.insert(import_line, make_merkle_import('LocalDepWithLampe-2.0.0'))

    f.seek(0)
    f.writelines(content)

cat ./user_files/append_to_TestDep.lean >> ./lampe/TestDep-0.0.0.lean
