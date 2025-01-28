#! /bin/sh

pushd ../

cargo build


pushd Lampe/

lake exe cache get
lake build

popd && popd

