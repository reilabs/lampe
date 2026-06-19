"""Shared helper for in-place Lean artifact generators.

`update_region` rewrites only the text strictly between a pair of marker
comments:

    -- BEGIN generated {label} --
    -- END generated {label} --

Everything outside the markers (header docstring, namespace, hand-written
defs) is left untouched. Re-running with the same body is a no-op.
"""

import sys


def _marker(kind: str, label: str) -> str:
    return f"-- {kind} generated {label} --"


def _find_unique(text: str, marker: str, path: str) -> int:
    first = text.find(marker)
    if first == -1:
        print(f"error: marker {marker!r} not found in {path}", file=sys.stderr)
        sys.exit(1)
    if text.find(marker, first + len(marker)) != -1:
        print(
            f"error: marker {marker!r} appears more than once in {path}",
            file=sys.stderr,
        )
        sys.exit(1)
    return first


def update_region(path: str, body: str, *, label: str) -> None:
    """Replace the text between the `{label}` markers in `path` with `body`.

    The body is wrapped with a single blank-line gap from the markers and
    exactly one trailing newline, so repeated runs converge.
    """
    begin = _marker("BEGIN", label)
    end = _marker("END", label)

    with open(path, encoding="utf-8") as f:
        text = f.read()

    begin_at = _find_unique(text, begin, path)
    end_at = _find_unique(text, end, path)
    if end_at < begin_at:
        print(
            f"error: END marker precedes BEGIN marker for {label!r} in {path}",
            file=sys.stderr,
        )
        sys.exit(1)

    prefix = text[: begin_at + len(begin)]
    suffix = text[end_at:]

    new_region = "\n" + body.strip("\n") + "\n"
    new_text = prefix + new_region + suffix

    if new_text == text:
        print(f"{path}: up to date", file=sys.stderr)
        return

    with open(path, "w", encoding="utf-8") as f:
        f.write(new_text)
    print(f"{path}: regenerated {label}", file=sys.stderr)
