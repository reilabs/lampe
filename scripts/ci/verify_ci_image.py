#!/usr/bin/env python3
import argparse
import subprocess
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify CI image exists in GHCR")
    parser.add_argument("image", help="Full image reference (ghcr.io/org/name:tag)")
    args = parser.parse_args()

    try:
        subprocess.run(
            ["docker", "manifest", "inspect", args.image],
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError:
        message = (
            "CI image not found: {image}\n"
            "Run the CI Image workflow to publish it before re-running CI.\n"
        ).format(image=args.image)
        sys.stderr.write(message)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
