#!/usr/bin/env python3
"""Reference secp256r1 (NIST P-256) ECDSA test vector generator.

Mirror of `scripts/gen/secp256k1_ref.py` for the other Noir foreign-call
curve. Uses pure-Python `ecdsa` with RFC 6979 deterministic signing so
outputs regenerate identically. Vectors are checked via `native_decide`.

Usage:
    python3 scripts/gen/secp256r1_ref.py <path/to/Ecdsa.lean>
"""

import hashlib
import sys

from _lean import update_region

try:
    from ecdsa import SigningKey, NIST256p, util
except ImportError:
    print("error: pip install --user --break-system-packages ecdsa", file=sys.stderr)
    sys.exit(1)

CURVE = NIST256p
LABEL = "secp256r1 test vectors"


def bytes_to_lean_array(bs: bytes) -> str:
    return "#[" + ", ".join(f"0x{b:02x}#8" for b in bs) + "]"


def sign(sk_hex: str, msg: bytes):
    sk = SigningKey.from_string(bytes.fromhex(sk_hex), curve=CURVE)
    vk = sk.verifying_key
    msg_hash = hashlib.sha256(msg).digest()
    sig = sk.sign_digest_deterministic(
        msg_hash,
        hashfunc=hashlib.sha256,
        sigencode=util.sigencode_string,
    )
    pk = vk.to_string()
    return pk[:32], pk[32:], sig, msg_hash


SK_ALL_ONES = "01" * 32
SK_SEQ = "".join(f"{i:02x}" for i in range(1, 33))


def build_body() -> str:
    blocks = []

    pk_x, pk_y, sig, msg = sign(SK_ALL_ONES, b"Lampe ECDSA test vector")
    blocks.append("\n".join([
        '-- valid signature: sk = 0x01..01, msg = "Lampe ECDSA test vector"',
        f"private def validSimplePkX : Array (BitVec 8) := {bytes_to_lean_array(pk_x)}",
        f"private def validSimplePkY : Array (BitVec 8) := {bytes_to_lean_array(pk_y)}",
        f"private def validSimpleSig : Array (BitVec 8) := {bytes_to_lean_array(sig)}",
        f"private def validSimpleMsg : Array (BitVec 8) := {bytes_to_lean_array(msg)}",
        "example :",
        "    verifyBytes validSimplePkX validSimplePkY validSimpleSig validSimpleMsg = true := by",
        "  native_decide",
    ]))

    pk_x, pk_y, sig, msg = sign(SK_SEQ, b"another message")
    blocks.append("\n".join([
        '-- valid signature: sk = 0x01..20, msg = "another message"',
        f"private def validSeqPkX : Array (BitVec 8) := {bytes_to_lean_array(pk_x)}",
        f"private def validSeqPkY : Array (BitVec 8) := {bytes_to_lean_array(pk_y)}",
        f"private def validSeqSig : Array (BitVec 8) := {bytes_to_lean_array(sig)}",
        f"private def validSeqMsg : Array (BitVec 8) := {bytes_to_lean_array(msg)}",
        "example :",
        "    verifyBytes validSeqPkX validSeqPkY validSeqSig validSeqMsg = true := by",
        "  native_decide",
    ]))

    # Tamper validSimple by flipping one bit; reuse its pk/msg defs.
    _, _, sig, _ = sign(SK_ALL_ONES, b"Lampe ECDSA test vector")
    tampered = bytes([sig[0] ^ 0x01]) + sig[1:]
    blocks.append("\n".join([
        "-- tampered: validSimple sig with one bit flipped → reject",
        f"private def tamperedSig : Array (BitVec 8) := {bytes_to_lean_array(tampered)}",
        "example :",
        "    verifyBytes validSimplePkX validSimplePkY tamperedSig validSimpleMsg = false := by",
        "  native_decide",
    ]))

    return "\n\n".join(blocks)


def main():
    if len(sys.argv) != 2:
        print("usage: secp256r1_ref.py <path/to/Ecdsa.lean>", file=sys.stderr)
        sys.exit(1)
    update_region(sys.argv[1], build_body(), label=LABEL)


if __name__ == "__main__":
    main()
