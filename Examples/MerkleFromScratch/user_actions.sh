#!/usr/bin/bash
set -euxo pipefail

cp ./user_files/Field.lean ./lampe/Merkle
LAST_IMPORT="$(cat lampe/Merkle.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport Merkle.Field/g" lampe/Merkle.lean

cp ./user_files/Ref.lean ./lampe/Merkle
LAST_IMPORT="$(cat lampe/Merkle.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport Merkle.Ref/g" lampe/Merkle.lean

cp ./user_files/Spec.lean ./lampe/Merkle
LAST_IMPORT="$(cat lampe/Merkle.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport Merkle.Spec/g" lampe/Merkle.lean

cat ./user_files/append_to_Merkle.lean >> ./lampe/Merkle.lean

echo '
[[require]]
name = "proven-zk"
git = "https://github.com/reilabs/proven-zk"
rev = "4.15"
' >> ./lampe/lakefile.toml