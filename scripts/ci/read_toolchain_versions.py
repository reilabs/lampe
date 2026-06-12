#!/usr/bin/env python3
import hashlib
import json
import os
import pathlib
import re
import tomllib


def read_toml(path: pathlib.Path) -> dict:
    return tomllib.loads(path.read_text())


def normalize_tag(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "-", value)


def read_rust_stable(root: pathlib.Path) -> str:
    rust_toolchain = read_toml(root / "rust-toolchain.toml")
    return rust_toolchain["toolchain"]["channel"]


def read_lean_toolchain(root: pathlib.Path) -> str:
    lampe_toolchain = (root / "Lampe" / "lean-toolchain").read_text().strip()
    stdlib_toolchain = (root / "stdlib" / "lampe" / "lean-toolchain").read_text().strip()
    if stdlib_toolchain and stdlib_toolchain != lampe_toolchain:
        raise SystemExit(
            "Lampe and stdlib lean-toolchain versions differ; update them together."
        )
    return lampe_toolchain


def lean_version_for_tag(lean_toolchain: str) -> str:
    if ":" in lean_toolchain:
        lean_toolchain = lean_toolchain.split(":", 1)[1]
    return normalize_tag(lean_toolchain)


def read_noir_rev(root: pathlib.Path) -> str:
    cargo = read_toml(root / "Cargo.toml")
    return cargo["dependencies"]["noirc_driver"]["rev"]


def read_mathlib_rev_from(manifest_path: pathlib.Path) -> str:
    manifest = json.loads(manifest_path.read_text())
    for package in manifest["packages"]:
        if package["name"] == "mathlib":
            return package["rev"]
    raise SystemExit(f"mathlib package not found in {manifest_path}")


def read_mathlib_rev(root: pathlib.Path) -> str:
    lampe_rev = read_mathlib_rev_from(root / "Lampe" / "lake-manifest.json")
    stdlib_rev = read_mathlib_rev_from(root / "stdlib" / "lampe" / "lake-manifest.json")
    if stdlib_rev != lampe_rev:
        raise SystemExit(
            "Lampe and stdlib mathlib revisions differ; update them together."
        )
    return lampe_rev


def read_docker_context_hash(root: pathlib.Path) -> str:
    # The tag must change whenever the image recipe changes, otherwise the
    # existence check in build-ci-image keeps serving the old image forever.
    # The hash covers every file the Dockerfile COPYs into the image plus the
    # recipe itself: the whole docker/ci/ directory and the COPY'd repo files.
    paths = [
        path
        for path in (root / "docker" / "ci").rglob("*")
        if path.is_file()
    ]
    paths += [
        root / "scripts" / "requirements.txt",
        root / "Lampe" / "lakefile.lean",
        root / "Lampe" / "lake-manifest.json",
    ]
    paths.sort()
    digest = hashlib.sha256()
    for path in paths:
        digest.update(path.relative_to(root).as_posix().encode())
        digest.update(path.read_bytes())
    return digest.hexdigest()[:8]


def write_output(key: str, value: str) -> None:
    output_path = os.environ.get("GITHUB_OUTPUT")
    if output_path:
        with open(output_path, "a") as output:
            output.write(f"{key}={value}\n")
    else:
        print(f"{key}={value}")


def main() -> None:
    root = pathlib.Path(__file__).resolve().parents[2]
    rust_stable = read_rust_stable(root)
    lean_toolchain = read_lean_toolchain(root)
    noir_rev = read_noir_rev(root)
    mathlib_rev = read_mathlib_rev(root)

    lean_tag = lean_version_for_tag(lean_toolchain)
    noir_short = normalize_tag(noir_rev)[:4]
    mathlib_short = normalize_tag(mathlib_rev)[:8]
    context_short = read_docker_context_hash(root)
    image_tag = (
        f"rust-{normalize_tag(rust_stable)}"
        f"-lean-{lean_tag}"
        f"-noir-{noir_short}"
        f"-mathlib-{mathlib_short}"
        f"-ctx-{context_short}"
    )

    write_output("rust_stable", rust_stable)
    write_output("lean_toolchain", lean_toolchain)
    write_output("noir_rev", noir_rev)
    write_output("mathlib_rev", mathlib_rev)
    write_output("image_tag", image_tag)


if __name__ == "__main__":
    main()
