#!/usr/bin/env python3
"""Reference BLAKE3 test vector generator.

Uses the official BLAKE3 Python binding (pip install blake3), which is
maintained by the BLAKE3 team and known to match the official test
vectors at https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/

The input pattern matches the canonical test vector spec:
  input[i] = i % 251

Lampe's concrete BLAKE3 implementation is validated against these
vectors via `native_decide`.

Usage:
    python3 scripts/gen/blake3_ref.py <path/to/Blake3.lean>
"""

import sys

from _lean import update_region

try:
    import blake3
except ImportError:
    print("error: pip install --user --break-system-packages blake3", file=sys.stderr)
    sys.exit(1)


# Lengths chosen to cover key boundaries in the BLAKE3 algorithm:
#   0    : empty input (the canonical hash of "")
#   1    : single byte
#   63   : one byte short of a block
#   64   : exactly one block
#   65   : one byte past a block boundary
#   1023 : one byte short of a chunk (16 blocks, no tree)
#   1024 : exactly one chunk (single-chunk mode, ROOT flag on last block)
#   1025 : just over a chunk (triggers Merkle tree mode: 1 full chunk + 1 byte)
#   2048 : two full chunks (tree depth 1, symmetric)
TEST_LENGTHS = [0, 1, 63, 64, 65, 1023, 1024, 1025, 2048]

NAMES = {
    0: "empty",
    1: "oneByte",
    63: "underBlock",
    64: "oneBlock",
    65: "overBlock",
    1023: "underChunk",
    1024: "oneChunk",
    1025: "overChunk",
    2048: "twoChunks",
}


def canonical_input(n: int) -> bytes:
    return bytes(i % 251 for i in range(n))


def lane(b: int) -> str:
    return f"0x{b:02x}#8"


def vector_lines(name: str, n: int) -> list[str]:
    inp = canonical_input(n)
    digest = blake3.blake3(inp).digest()
    out_lanes = ", ".join(lane(b) for b in digest)
    lines = [f"-- {name}: input = [i % 251 for i in 0..{n}], len = {n}"]
    lines.append(f"private def {name}In : Array (BitVec 8) :=")
    if n == 0:
        lines.append("  #[]")
    else:
        lines.append(
            f"  ((List.range {n}).map (fun i => BitVec.ofNat 8 (i % 251))).toArray"
        )
    lines.append(f"private def {name}Out : Array (BitVec 8) :=")
    lines.append(f"  #[{out_lanes}]")
    lines.append(f"example : blake3HashBytes {name}In = {name}Out := by native_decide")
    return lines


def build_body() -> str:
    blocks = ["\n".join(vector_lines(NAMES[n], n)) for n in TEST_LENGTHS]
    return "\n\n".join(blocks)


def main():
    if len(sys.argv) != 2:
        print("usage: blake3_ref.py <path/to/Blake3.lean>", file=sys.stderr)
        sys.exit(1)
    update_region(sys.argv[1], build_body(), label="blake3 test vectors")


if __name__ == "__main__":
    main()
