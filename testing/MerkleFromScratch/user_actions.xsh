#!/usr/bin/env xonsh

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

# This exists to run the test against the current version of Lampe, rather than whatever is at the
# repository's head.
lampe_dependency = [
    '[[require]]\n',
    'name = "Lampe"\n',
    'path = "../../../Lampe"\n',
    '\n'
]

# This exists to run the test against the current version of Lampe, rather than whatever is at the
# repository's head.
stdlib_dependency = [
    '[[require]]\n',
    'name = "std-1.0.0-beta.3"\n',
    'path = "../../../stdlib/lampe"\n',
    '\n'
]

with open('./lampe/lakefile.toml', 'a') as f:
    f.writelines(proven_zk_dependency)
    f.writelines(lampe_dependency)
    f.writelines(stdlib_dependency)
