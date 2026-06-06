#!/usr/bin/env python3
"""Reference BLAKE2s test vector generator.

Uses Python's stdlib `hashlib.blake2s`, which is a thin wrapper around
the BLAKE2 reference implementation (libb2). No external dependency.

BLAKE2s is the 32-bit variant of BLAKE2 with a 32-byte digest and a
64-byte (16 u32 words) message block. This script emits Lean array
literals matching the format Lampe's `Crypto.Blake2s` test vectors
expect (see `Lampe/Lampe/Crypto/Blake2s.lean`).

Reference: RFC 7693 (Appendix A.1 has the BLAKE2s test vector for
"abc").

Inputs chosen to cover key boundaries in the algorithm:
  empty       : 0 bytes (no data, just the IV-XOR-parameter-block
                finalisation)
  abc         : the canonical RFC 7693 test vector
  oneBlock    : 64 bytes (exactly one BLAKE2s message block)
  overBlock   : 65 bytes (just past block boundary, exercises the
                two-block path with non-aligned final block length)

Lampe's concrete BLAKE2s implementation is validated against these
vectors via `native_decide`.
"""

import hashlib


def lean_byte(b: int) -> str:
    return f"0x{b:02x}#8"


def emit_vector(name: str, inp: bytes, description: str) -> None:
    digest = hashlib.blake2s(inp).digest()
    in_lanes = ", ".join(lean_byte(b) for b in inp)
    out_lanes = ", ".join(lean_byte(b) for b in digest)

    print(f"-- {name}: {description}, input length = {len(inp)}")
    print(f"private def {name}In : Array (BitVec 8) :=")
    if len(inp) == 0:
        print(f"  #[]")
    elif len(inp) <= 16:
        print(f"  #[{in_lanes}]")
    else:
        # Use canonical i % 251 formulation for the boundary-length
        # inputs so the literal is short and human-readable.
        print(
            f"  ((List.range {len(inp)}).map "
            f"(fun i => BitVec.ofNat 8 (i % 251))).toArray"
        )
    print(f"private def {name}Out : Array (BitVec 8) :=")
    print(f"  #[{out_lanes}]")
    print(f"theorem blake2s_{name}_correct :")
    print(f"    blake2sHashBytes {name}In = {name}Out := by native_decide")
    print()


# Vectors for native_decide tests.
emit_vector("empty", b"", "RFC 7693 reference empty-input hash")
emit_vector("abc", b"abc", "RFC 7693 reference 'abc' hash")
emit_vector(
    "oneBlock",
    bytes(i % 251 for i in range(64)),
    "exactly one full BLAKE2s message block",
)
emit_vector(
    "overBlock",
    bytes(i % 251 for i in range(65)),
    "one byte past block boundary (two compressions)",
)
