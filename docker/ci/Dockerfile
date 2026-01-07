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
