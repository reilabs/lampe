#!/usr/bin/env python3
"""Reference BLAKE2s test vector generator.

Uses Python's stdlib `hashlib.blake2s`, which is a thin wrapper around
the BLAKE2 reference implementation (libb2). No external dependency.

BLAKE2s is the 32-bit variant of BLAKE2 with a 32-byte digest and a
64-byte (16 u32 words) message block.

Reference: RFC 7693 (Appendix A.1 has the BLAKE2s test vector for
"abc").

Inputs chosen to cover key boundaries in the algorithm:
  empty       : 0 bytes (IV-XOR-parameter-block finalisation only)
  abc         : the canonical RFC 7693 test vector
  oneBlock    : 64 bytes (exactly one BLAKE2s message block)
  overBlock   : 65 bytes (just past block boundary, two compressions)

Lampe's concrete BLAKE2s implementation is validated against these
vectors via `native_decide`.

Usage:
    python3 scripts/gen/blake2s_ref.py <path/to/Blake2s.lean>
"""

import hashlib
import sys

from _lean import update_region


def lean_byte(b: int) -> str:
    return f"0x{b:02x}#8"


def vector_lines(name: str, inp: bytes, description: str) -> list[str]:
    digest = hashlib.blake2s(inp).digest()
    in_lanes = ", ".join(lean_byte(b) for b in inp)
    out_lanes = ", ".join(lean_byte(b) for b in digest)

    lines = [f"-- {name}: {description}, input length = {len(inp)}"]
    lines.append(f"private def {name}In : Array (BitVec 8) :=")
    if len(inp) == 0:
        lines.append("  #[]")
    elif len(inp) <= 16:
        lines.append(f"  #[{in_lanes}]")
    else:
        # Canonical i % 251 formulation for the boundary-length inputs.
        lines.append(
            f"  ((List.range {len(inp)}).map "
            f"(fun i => BitVec.ofNat 8 (i % 251))).toArray"
        )
    lines.append(f"private def {name}Out : Array (BitVec 8) :=")
    lines.append(f"  #[{out_lanes}]")
    lines.append(
        f"example : blake2sHashBytes {name}In = {name}Out := by native_decide"
    )
    return lines


VECTORS = [
    ("empty", b"", "RFC 7693 reference"),
    ("abc", b"abc", "RFC 7693 reference"),
    ("oneBlock", bytes(i % 251 for i in range(64)),
     "exactly one full BLAKE2s message block"),
    ("overBlock", bytes(i % 251 for i in range(65)),
     "one byte past block boundary (two compressions)"),
]


def build_body() -> str:
    blocks = ["\n".join(vector_lines(n, inp, d)) for n, inp, d in VECTORS]
    return "\n\n".join(blocks)


def main():
    if len(sys.argv) != 2:
        print("usage: blake2s_ref.py <path/to/Blake2s.lean>", file=sys.stderr)
        sys.exit(1)
    update_region(sys.argv[1], build_body(), label="blake2s test vectors")


if __name__ == "__main__":
    main()
