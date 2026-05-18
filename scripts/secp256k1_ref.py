#!/usr/bin/env python3
"""Reference secp256k1 ECDSA test vector generator.

Uses the pure-Python `ecdsa` library (pip install ecdsa) which
implements RFC 6979 deterministic signing — so vectors regenerate
identically.

Outputs Lean test vectors comparing
  Lampe.Crypto.Secp256k1.verifyBytes pkX pkY sig msgHash
to the expected verification result, which is `true` for valid
signatures and `false` for tampered ones.

Lampe validates against these via native_decide. Since Barretenberg's
`__ecdsa_secp256k1` foreign call must produce the same outputs (it is
the standard FIPS 186-4 verification algorithm), agreement with the
Python reference transitively certifies agreement with Barretenberg.
"""

import hashlib
import sys

try:
    from ecdsa import SigningKey, SECP256k1, util
except ImportError:
    print("error: pip install --user --break-system-packages ecdsa", file=sys.stderr)
    sys.exit(1)


def bytes_to_lean_array(bs: bytes) -> str:
    """Render bytes as a Lean `Array (BitVec 8)` literal."""
    return "#[" + ", ".join(f"0x{b:02x}#8" for b in bs) + "]"


def emit_vector(name: str, sk_hex: str, msg: bytes, *, tamper: bool = False) -> None:
    sk = SigningKey.from_string(bytes.fromhex(sk_hex), curve=SECP256k1)
    vk = sk.verifying_key
    msg_hash = hashlib.sha256(msg).digest()
    # Deterministic (RFC 6979) signature so output is reproducible.
    sig = sk.sign_digest_deterministic(
        msg_hash,
        hashfunc=hashlib.sha256,
        sigencode=util.sigencode_string,  # raw 64-byte r||s
    )
    pk_str = vk.to_string()  # 64 bytes: x || y
    pk_x = pk_str[:32]
    pk_y = pk_str[32:]

    if tamper:
        # Flip a single bit in the signature -> verification must fail.
        sig = bytes([sig[0] ^ 0x01]) + sig[1:]
    expected = "false" if tamper else "true"

    note = "tampered signature → reject" if tamper else "valid signature → accept"
    print(f"-- {name}: msg = {msg!r}, sk = 0x{sk_hex}; {note}")
    print(f"private def {name}PkX : Array (BitVec 8) := {bytes_to_lean_array(pk_x)}")
    print(f"private def {name}PkY : Array (BitVec 8) := {bytes_to_lean_array(pk_y)}")
    print(f"private def {name}Sig : Array (BitVec 8) := {bytes_to_lean_array(sig)}")
    print(f"private def {name}Msg : Array (BitVec 8) := {bytes_to_lean_array(msg_hash)}")
    print(f"theorem secp256k1_{name}_correct :")
    print(f"    verifyBytes {name}PkX {name}PkY {name}Sig {name}Msg = {expected} := by")
    print(f"  native_decide")
    print()


# Fixed seed private keys for reproducibility.
SK_ALL_ONES = "01" * 32
SK_SEQ = "".join(f"{i:02x}" for i in range(1, 33))  # 0x01..0x20

emit_vector("validSimple", SK_ALL_ONES, b"Lampe ECDSA test vector")
emit_vector("validSeq",    SK_SEQ,      b"another message")
emit_vector("tampered",    SK_ALL_ONES, b"Lampe ECDSA test vector", tamper=True)
