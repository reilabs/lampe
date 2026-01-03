#!/usr/bin/env python3

import os
import sys


def main() -> None:
    args = [arg for arg in sys.argv[1:] if arg not in ("-Wl,-Bstatic", "-Wl,-Bdynamic")]
    cc = os.environ.get("LEAN_CC_REAL", "cc")
    os.execvp(cc, [cc, *args])


if __name__ == "__main__":
    main()
