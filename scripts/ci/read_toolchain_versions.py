#!/usr/bin/env python3
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

    lean_tag = lean_version_for_tag(lean_toolchain)
    noir_short = normalize_tag(noir_rev)[:4]
    image_tag = (
        f"rust-{normalize_tag(rust_stable)}"
        f"-lean-{lean_tag}"
        f"-noir-{noir_short}"
    )

    write_output("rust_stable", rust_stable)
    write_output("lean_toolchain", lean_toolchain)
    write_output("noir_rev", noir_rev)
    write_output("image_tag", image_tag)


if __name__ == "__main__":
    main()
