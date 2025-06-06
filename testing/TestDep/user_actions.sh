#!/usr/bin/env bash
set -euxo pipefail

LAST_IMPORT="$(cat lampe/TestDep-0.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «GitDepWithLampe-0.0.0».Extracted/g" lampe/TestDep-0.0.0.lean

LAST_IMPORT="$(cat lampe/TestDep-0.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «GitDepWithLampe-1.0.0».Extracted/g" lampe/TestDep-0.0.0.lean

LAST_IMPORT="$(cat lampe/TestDep-0.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «GitDepWithLampe-2.0.0».Extracted/g" lampe/TestDep-0.0.0.lean

LAST_IMPORT="$(cat lampe/TestDep-0.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «LocalDepWithLampe-0.0.0».Extracted/g" lampe/TestDep-0.0.0.lean

LAST_IMPORT="$(cat lampe/TestDep-0.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «LocalDepWithLampe-1.0.0».Extracted/g" lampe/TestDep-0.0.0.lean

LAST_IMPORT="$(cat lampe/TestDep-0.0.0.lean | grep "^import" | tail -n 1)"
sed -i -e "s/$LAST_IMPORT/$LAST_IMPORT\nimport «LocalDepWithLampe-2.0.0».Extracted/g" lampe/TestDep-0.0.0.lean

cat ./user_files/append_to_TestDep.lean >> ./lampe/TestDep-0.0.0.lean
