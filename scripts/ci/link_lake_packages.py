#!/usr/bin/env python3
"""Symlink <lampe_dir>/.lake/packages at the shared $LAKE_PKG_DIR.

Pointing each workspace's `.lake/packages` at the shared dir lets every
lake invocation in a CI run reuse the same mathlib / proven-zk / batteries
clones. The lakefile and manifest both spell the dir as `.lake/packages`,
so the symlink is enough; no further rewriting is required. A no-op when
LAKE_PKG_DIR is unset.
"""
import os
import pathlib
import shutil
import sys


def link_packages_dir(lampe_dir: pathlib.Path) -> None:
    packages_root_env = os.environ.get("LAKE_PKG_DIR")
    if not packages_root_env:
        return
    packages_root = pathlib.Path(packages_root_env)
    packages_root.mkdir(parents=True, exist_ok=True)
    lake_dir = lampe_dir / ".lake"
    lake_dir.mkdir(parents=True, exist_ok=True)
    packages_link = lake_dir / "packages"
    if packages_link.is_symlink() or packages_link.exists():
        if packages_link.is_symlink() or not packages_link.is_dir():
            packages_link.unlink()
        else:
            shutil.rmtree(packages_link)
    packages_link.symlink_to(
        os.path.relpath(packages_root, lake_dir),
        target_is_directory=True,
    )


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} <lampe_dir>")
    link_packages_dir(pathlib.Path(sys.argv[1]))


if __name__ == "__main__":
    main()
