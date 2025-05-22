#!/usr/bin/bash
set -euxo pipefail

cp ./user_files/Field.lean ./lampe/Merkle-1.0.0
LAST_IMPORT="$(cat lampe/Merkle-1.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «Merkle-1.0.0».Field/g" lampe/Merkle-1.0.0.lean

cp ./user_files/Ref.lean ./lampe/Merkle-1.0.0
LAST_IMPORT="$(cat lampe/Merkle-1.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «Merkle-1.0.0».Ref/g" lampe/Merkle-1.0.0.lean

cp ./user_files/Spec.lean ./lampe/Merkle-1.0.0
LAST_IMPORT="$(cat lampe/Merkle-1.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «Merkle-1.0.0».Spec/g" lampe/Merkle-1.0.0.lean

cat ./user_files/append_to_Merkle.lean >> ./lampe/Merkle-1.0.0.lean

echo '
[[require]]
name = "proven-zk"
git = "https://github.com/reilabs/proven-zk"
rev = "4.15"
' >> ./lampe/lakefile.toml