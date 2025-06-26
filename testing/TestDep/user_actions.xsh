#!/usr/bin/env xonsh

$RAISE_SUBPROC_ERROR = True

def make_merkle_import(libname):
    return "import «" + libname + "».Extracted\n"

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
