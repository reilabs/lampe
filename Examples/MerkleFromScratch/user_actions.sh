#!/usr/bin/bash
set -euxo pipefail

cp ./user_files/Field.lean ./lampe/Merkle
echo "import Merkle.Field" >> ./lampe/Merkle.lean

cp ./user_files/Ref.lean ./lampe/Merkle
echo "import Merkle.Ref" >> ./lampe/Merkle.lean

cp ./user_files/Spec.lean ./lampe/Merkle
echo "import Merkle.Spec" >> ./lampe/Merkle.lean

echo '[[require]]
name = "proven-zk"
git = "https://github.com/reilabs/proven-zk"
rev = "4.15"
' >> ./lampe/lakefile.toml
