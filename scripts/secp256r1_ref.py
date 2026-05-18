#!/usr/bin/env python3
"""Reference secp256r1 (NIST P-256) ECDSA test vector generator.

Mirror of `scripts/secp256k1_ref.py` for the other Noir foreign-call
curve. Uses pure-Python `ecdsa` with RFC 6979 deterministic signing
so outputs regenerate identically.
"""

import hashlib
import sys

try:
    from ecdsa import SigningKey, NIST256p, util
except ImportError:
    print("error: pip install --user --break-system-packages ecdsa", file=sys.stderr)
    sys.exit(1)


def bytes_to_lean_array(bs: bytes) -> str:
    return "#[" + ", ".join(f"0x{b:02x}#8" for b in bs) + "]"


def emit_vector(name: str, sk_hex: str, msg: bytes, *, tamper: bool = False) -> None:
    sk = SigningKey.from_string(bytes.fromhex(sk_hex), curve=NIST256p)
    vk = sk.verifying_key
    msg_hash = hashlib.sha256(msg).digest()
    sig = sk.sign_digest_deterministic(
        msg_hash,
        hashfunc=hashlib.sha256,
        sigencode=util.sigencode_string,
    )
    pk_str = vk.to_string()
    pk_x = pk_str[:32]
    pk_y = pk_str[32:]

    if tamper:
        sig = bytes([sig[0] ^ 0x01]) + sig[1:]
    expected = "false" if tamper else "true"

    note = "tampered signature → reject" if tamper else "valid signature → accept"
    print(f"-- {name}: msg = {msg!r}, sk = 0x{sk_hex}; {note}")
    print(f"private def {name}PkX : Array (BitVec 8) := {bytes_to_lean_array(pk_x)}")
    print(f"private def {name}PkY : Array (BitVec 8) := {bytes_to_lean_array(pk_y)}")
    print(f"private def {name}Sig : Array (BitVec 8) := {bytes_to_lean_array(sig)}")
    print(f"private def {name}Msg : Array (BitVec 8) := {bytes_to_lean_array(msg_hash)}")
    print(f"theorem secp256r1_{name}_correct :")
    print(f"    verifyBytes {name}PkX {name}PkY {name}Sig {name}Msg = {expected} := by")
    print(f"  native_decide")
    print()


SK_ALL_ONES = "01" * 32
SK_SEQ = "".join(f"{i:02x}" for i in range(1, 33))

emit_vector("validSimple", SK_ALL_ONES, b"Lampe ECDSA test vector")
emit_vector("validSeq",    SK_SEQ,      b"another message")
emit_vector("tampered",    SK_ALL_ONES, b"Lampe ECDSA test vector", tamper=True)
