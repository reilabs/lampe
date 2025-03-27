#!/usr/bin/bash
set -euxo pipefail

cp ./../Merkle/lampe/Field.lean ./lampe
echo "import Field" >> ./lampe/Merkle.lean
echo "" >> ./lampe/lakefile.toml
echo "[[lean_lib]]" >> ./lampe/lakefile.toml
echo "name = \"Field\"" >> ./lampe/lakefile.toml

cp ./../Merkle/lampe/Ref.lean ./lampe
echo "import Ref" >> ./lampe/Merkle.lean
echo "" >> ./lampe/lakefile.toml
echo "[[lean_lib]]" >> ./lampe/lakefile.toml
echo "name = \"Ref\"" >> ./lampe/lakefile.toml

cp ./../Merkle/lampe/Spec.lean ./lampe
echo "import Spec" >> ./lampe/Merkle.lean
echo "" >> ./lampe/lakefile.toml
echo "[[lean_lib]]" >> ./lampe/lakefile.toml
echo "name = \"Spec\"" >> ./lampe/lakefile.toml
