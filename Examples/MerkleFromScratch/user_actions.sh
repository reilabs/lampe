#!/usr/bin/bash
set -euxo pipefail

cp ./user_files/Field.lean ./lampe
echo "import Field" >> ./lampe/Merkle.lean
echo "" >> ./lampe/lakefile.toml
echo "[[lean_lib]]" >> ./lampe/lakefile.toml
echo "name = \"Field\"" >> ./lampe/lakefile.toml

cp ./user_files/Ref.lean ./lampe
echo "import Ref" >> ./lampe/Merkle.lean
echo "" >> ./lampe/lakefile.toml
echo "[[lean_lib]]" >> ./lampe/lakefile.toml
echo "name = \"Ref\"" >> ./lampe/lakefile.toml

cp ./user_files/Spec.lean ./lampe
echo "import Spec" >> ./lampe/Merkle.lean
echo "" >> ./lampe/lakefile.toml
echo "[[lean_lib]]" >> ./lampe/lakefile.toml
echo "name = \"Spec\"" >> ./lampe/lakefile.toml
