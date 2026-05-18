#!/usr/bin/env python3
"""Reference BLAKE3 test vector generator.

Uses the official BLAKE3 Python binding (pip install blake3), which is
maintained by the BLAKE3 team and known to match the official test
vectors at https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/

The input pattern matches the canonical test vector spec:
  input[i] = i % 251

Lampe's concrete BLAKE3 implementation is validated against these
vectors via native_decide theorems. Since Barretenberg's foreign
__blake3 must produce the same outputs (any divergence would break
every Noir program that hashes blake3), matching these vectors
transitively certifies agreement with Barretenberg.
"""

import sys

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


def canonical_input(n: int) -> bytes:
    return bytes(i % 251 for i in range(n))


def emit_test_vector(name: str, n: int) -> None:
    inp = canonical_input(n)
    digest = blake3.blake3(inp).digest()
    # Lean BitVec 8 literal: 0xNN#8
    def lane(b): return f"0x{b:02x}#8"
    out_lanes = ", ".join(lane(b) for b in digest)
    print(f"-- {name}: input = [i % 251 for i in 0..{n}], len = {n}")
    # Input: use the canonical formula i % 251 rather than 1024+ literals.
    print(f"private def {name}In : Array (BitVec 8) :=")
    if n == 0:
        print(f"  #[]")
    else:
        print(f"  ((List.range {n}).map (fun i => BitVec.ofNat 8 (i % 251))).toArray")
    print(f"private def {name}Out : Array (BitVec 8) :=")
    print(f"  #[{out_lanes}]")
    print(f"theorem blake3_{name}_correct :")
    print(f"    blake3HashBytes {name}In = {name}Out := by native_decide")
    print()


# Tag-friendly names for the lengths
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

for n in TEST_LENGTHS:
    emit_test_vector(NAMES[n], n)
