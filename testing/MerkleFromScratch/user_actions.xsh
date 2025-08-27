#!/usr/bin/env xonsh

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

$RAISE_SUBPROC_ERROR = True

def make_merkle_import(name):
    return "import «Merkle-1.0.0»." + name + "\n"

cp ./user_files/Field.lean ./lampe/Merkle-1.0.0
cp ./user_files/Ref.lean ./lampe/Merkle-1.0.0
cp ./user_files/Spec.lean ./lampe/Merkle-1.0.0

with open('./lampe/Merkle-1.0.0.lean', 'r+') as f:
    content = f.readlines()

    for i, line in enumerate(content):
        if line.startswith('import'):
            import_line = i
            break

    content.insert(import_line, make_merkle_import('Field'))
    content.insert(import_line + 1, make_merkle_import('Ref'))
    content.insert(import_line + 2, make_merkle_import('Spec'))

    f.seek(0)
    f.writelines(content)

cat ./user_files/append_to_Merkle.lean >> ./lampe/Merkle-1.0.0.lean

proven_zk_dependency = [
    '[[require]]\n',
    'name = "proven-zk"\n',
    'git = "https://github.com/reilabs/proven-zk"\n',
    'rev = "45b4de912bf9ae37f0a42df4d4adcf24c8348fb3"\n',
    '\n'
]

with open('./lampe/lakefile.toml', 'a') as f:
    f.writelines(proven_zk_dependency)

change_toml_required_dep_to_path_by_regex('./lampe/lakefile.toml', '^Lampe$', '../../../Lampe')
change_toml_required_dep_to_path_by_regex('./lampe/lakefile.toml', '^std-.*$', '../../../stdlib/lampe')