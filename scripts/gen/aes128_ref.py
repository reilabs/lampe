#!/usr/bin/env python3
"""Reference AES-128-CBC implementation for test vector generation.

Wraps the `cryptography` library's AES-128-CBC primitive together with
PKCS#7 padding, matching the behavior of Noir's `std::aes128::aes128_encrypt`
wrapper. The Barretenberg `aes128_encrypt` foreign builtin operates on
already-padded input (multiple-of-16 bytes); the stdlib wrapper layers
PKCS#7 padding on top.

Anchored against NIST SP 800-38A Appendix F.2.1 (AES-128-CBC encryption
example): for `key = 2b7e151628aed2a6abf7158809cf4f3c`,
`IV = 000102030405060708090a0b0c0d0e0f`,
plaintext = the four 16-byte blocks given in §F.2.1, ciphertext blocks
match what F.2.1 publishes. (The wrapper additionally appends a 16-byte
PKCS#7 padding block; the F.2.1 blocks themselves are still the prefix
of the verified output.)

Usage:
    python3 scripts/gen/aes128_ref.py <path/to/Aes128.lean>
"""

import sys

from _lean import update_region

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives import padding


NIST_KEY = bytes.fromhex("2b7e151628aed2a6abf7158809cf4f3c")
NIST_IV = bytes.fromhex("000102030405060708090a0b0c0d0e0f")
NIST_PT_F21 = bytes.fromhex(
    "6bc1bee22e409f96e93d7e117393172a"
    "ae2d8a571e03ac9c9eb76fac45af8e51"
    "30c81c46a35ce411e5fbc1191a0a52ef"
    "f69f2445df4f9b17ad2b417be66c3710"
)
# NIST SP 800-38A §F.2.1 expected ciphertext (no padding).
NIST_CT_F21_RAW = bytes.fromhex(
    "7649abac8119b246cee98e9b12e9197d"
    "5086cb9b507219ee95db113a917678b2"
    "73bed6b8e3c1743b7116e69e22229516"
    "3ff1caa1681fac09120eca307586e1a7"
)


def aes128_cbc_pkcs7(key: bytes, iv: bytes, pt: bytes) -> bytes:
    assert len(key) == 16
    assert len(iv) == 16
    padder = padding.PKCS7(128).padder()
    padded = padder.update(pt) + padder.finalize()
    cipher = Cipher(algorithms.AES(key), modes.CBC(iv))
    enc = cipher.encryptor()
    return enc.update(padded) + enc.finalize()


# Sanity: the toolchain reproduces NIST §F.2.1 (raw, unpadded portion).
_check = aes128_cbc_pkcs7(NIST_KEY, NIST_IV, NIST_PT_F21)
assert _check[:64] == NIST_CT_F21_RAW, "NIST SP 800-38A F.2.1 mismatch"


def fmt_byte(x: int) -> str:
    return f"0x{x:02x}#8"


def fmt_bytes(b: bytes) -> str:
    return "[" + ", ".join(fmt_byte(v) for v in b) + "]"


def vector_lines(name: str, key: bytes, iv: bytes, pt: bytes,
                 section: str, comment: str) -> list[str]:
    ct = aes128_cbc_pkcs7(key, iv, pt)
    n_in = len(pt)
    n_out = len(ct)
    lines = [f"/-! {section} -/", ""]
    lines.extend(comment.splitlines())
    lines.append(
        f"private def {name}Key : List.Vector (BitVec 8) 16 := ⟨{fmt_bytes(key)}, by decide⟩"
    )
    lines.append(
        f"private def {name}Iv : List.Vector (BitVec 8) 16 := ⟨{fmt_bytes(iv)}, by decide⟩"
    )
    lines.append(
        f"private def {name}In : List.Vector (BitVec 8) {n_in} := ⟨{fmt_bytes(pt)}, by decide⟩"
    )
    lines.append(
        f"private def {name}Out : List.Vector (BitVec 8) {n_out} := ⟨{fmt_bytes(ct)}, by decide⟩"
    )
    lines.append(f"example :")
    lines.append(
        f"    (aes128CbcEncryptPkcs7 {name}Key {name}Iv {name}In).toList "
        f"= {name}Out.toList := by native_decide"
    )
    return lines


VECTORS = [
    (
        "empty", NIST_KEY, NIST_IV, b"",
        "### Vector 1: empty input — pure padding block",
        "-- Empty input — full 16-byte PKCS#7 padding block (0x10 × 16).",
    ),
    (
        "oneBlock", NIST_KEY, NIST_IV, NIST_PT_F21[:16],
        "### Vector 2: one full block — adds full 0x10×16 padding block",
        "-- Single 16-byte block; PKCS#7 still appends a full 0x10×16 padding block.",
    ),
    (
        "nistF21", NIST_KEY, NIST_IV, NIST_PT_F21,
        "### Vector 3: NIST SP 800-38A §F.2.1 (canonical anchor)",
        "-- NIST SP 800-38A §F.2.1 AES-128-CBC encryption example.\n"
        "-- First 64 bytes of expected output match §F.2.1 verbatim; the\n"
        "-- trailing 16 bytes are the encryption of the PKCS#7 padding block.",
    ),
    (
        "partialBlock", NIST_KEY, NIST_IV, NIST_PT_F21[:17],
        "### Vector 4: non-aligned 17-byte input",
        "-- 17-byte input — PKCS#7 pads with 15 × 0x0f to reach 32 bytes.",
    ),
    (
        "oneByte", NIST_KEY, NIST_IV, b"\x00",
        "### Vector 5: single byte",
        "-- Single zero byte — pads with 15 × 0x0f.",
    ),
]


def build_body() -> str:
    blocks = [
        "\n".join(vector_lines(name, key, iv, pt, section, comment))
        for name, key, iv, pt, section, comment in VECTORS
    ]
    return "\n\n".join(blocks)


def main():
    if len(sys.argv) != 2:
        print("usage: aes128_ref.py <path/to/Aes128.lean>", file=sys.stderr)
        sys.exit(1)
    update_region(sys.argv[1], build_body(), label="aes128 test vectors")


if __name__ == "__main__":
    main()
