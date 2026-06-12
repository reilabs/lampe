FROM ubuntu:22.04

ARG DEBIAN_FRONTEND=noninteractive
ARG RUST_TOOLCHAIN_STABLE=1.90.0
ARG RUST_TOOLCHAIN_NIGHTLY=nightly
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.21.0
ARG NOIR_REV=

ENV RUSTUP_HOME=/opt/rustup
ENV CARGO_HOME=/opt/cargo
ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/cargo/bin:/opt/elan/bin:/root/.local/bin:$PATH

COPY scripts/requirements.txt /tmp/requirements.txt

RUN apt-get update \
    && apt-get install -yq \
        ca-certificates \
        curl \
        git \
        build-essential \
        pkg-config \
        python3 \
        python3-pip \
        python3-venv \
        pipx \
        libc++-dev \
        libc++abi-dev \
        libgmp-dev \
        libuv1-dev \
        protobuf-compiler \
    && rm -rf /var/lib/apt/lists/*

RUN pipx install 'xonsh[full]' \
    && pipx runpip xonsh install -r /tmp/requirements.txt

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --no-modify-path --profile minimal \
    && rustup toolchain install ${RUST_TOOLCHAIN_STABLE} \
    && rustup component add rustfmt clippy --toolchain ${RUST_TOOLCHAIN_STABLE} \
    && rustup toolchain install ${RUST_TOOLCHAIN_NIGHTLY} \
    && rustup component add rustfmt --toolchain ${RUST_TOOLCHAIN_NIGHTLY}

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path \
    && elan toolchain install ${LEAN_TOOLCHAIN} \
    && elan default ${LEAN_TOOLCHAIN}

RUN if [ -n "$NOIR_REV" ]; then \
        git clone https://github.com/noir-lang/noir /opt/noir; \
        cd /opt/noir; \
        git checkout "$NOIR_REV"; \
        cargo build --release -p nargo_cli; \
        cp /opt/noir/target/release/nargo /usr/local/bin/nargo; \
        rm -rf /opt/noir/.git /opt/noir/target; \
    fi

# Bake mathlib's `.ltar` store into the image so CI jobs depend on neither
# mathlib's cloud olean cache nor GitHub-cache round-trips. Only the store
# (~0.4GB) ships in the image: a fully built dependency tree unpacks to ~8GB
# more, and GitHub's hosted runners guarantee only ~14GB free while
# container-job image pulls happen before any job step can free disk, so a
# tree-carrying image makes every pull a coin flip against the runner's free
# space. CI jobs instead clone the dependency sources into a host-side shared
# dir and `lake exe cache get` decompresses offline from this store.
#
# bake_mathlib_cache.sh populates the store at image-build time, cheapest
# source first:
#   1. `lake exe cache get-` (download only, no decompression) in the bake
#      workspace, when mathlib's cloud cache still serves the pinned rev.
#   2. Full source build + `lake exe cache pack` from the built tree.
# The bake workspace reuses Lampe's lakefile and manifest so the packed
# revisions always match the pin; lake needs only the config files (not the
# Lampe sources) to materialize and build dependency targets. Each step is
# gated on the store still being too small to be a complete mathlib cache
# (mathlib is ~7k modules, one `.ltar` per module).
#
# `cache pack` must run with the mathlib clone as the workspace root and with
# the dependency clones physically inside mathlib's own `.lake/packages`,
# mirroring mathlib's CI: `.ltar` archives store workspace-root-relative
# paths (`.lake/build/...` for mathlib itself, `.lake/packages/<dep>/...`
# for dependencies), and `cache get` in downstream workspaces relies on
# exactly that layout (it redirects mathlib's own modules to the package dir
# at decompression time and dependency modules resolve to the same relative
# paths). Packing from a downstream root, or with the dependencies behind a
# symlink, bakes wrong (downstream-prefixed or absolute) paths into the
# archives. The script therefore moves the dependencies under the mathlib
# root for the pack; mathlib's manifest pins exactly the revisions Lampe
# inherits, so lake accepts them as-is.
#
# Everything except the store is transient: the clones and build artifacts
# are deleted in the same RUN that created them, so they never reach a
# layer. An image with a missing or partial store would silently push every
# CI job back onto mathlib's cloud cache or a full source build, so the bake
# fails instead of shipping one.
ENV MATHLIB_CACHE_DIR=/opt/mathlib-cache

COPY Lampe/lean-toolchain Lampe/lakefile.lean Lampe/lake-manifest.json \
    docker/ci/bake_mathlib_cache.sh /opt/lake-bake/

RUN /opt/lake-bake/bake_mathlib_cache.sh
