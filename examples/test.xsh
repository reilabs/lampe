#!/usr/bin/env xonsh

from pathlib import Path

project_root = Path(__file__).parent.parent.resolve()
source @(project_root / "scripts" / "test.xsh")

if __name__ == "__main__":
    main()
