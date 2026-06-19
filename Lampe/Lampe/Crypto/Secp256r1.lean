import Lampe.Crypto.Ecdsa.Verify
import Lampe.Crypto.MathlibBridge
import Lampe.Crypto.Secp256r1.Prime
import Mathlib.Algebra.Field.ZMod

/-!
# secp256r1 / NIST P-256 — ECDSA curve

ECDSA verification on the curve `y² = x³ - 3·x + b` over the
NIST P-256 base field. Mirror of `Crypto/Secp256k1.lean` with the
P-256 parameters from FIPS 186-4 Appendix D.1.2.3.

References:
- FIPS 186-4 Appendix D.1.2.3 (curve parameters)
- FIPS 186-4 §6.4.2 (ECDSA verification)
-/

namespace Lampe.Crypto.Secp256r1

open Lampe

abbrev F : Type := Fp Secp256r1.prime

def W : WeierstrassCurve.Affine F :=
  { a₁ := 0
    a₂ := 0
    a₃ := 0
    a₄ := ((0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC : Nat) : F)
    a₆ := ((0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B : Nat) : F) }

def orderN : Nat :=
  0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

def Gx : F :=
  ((0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296 : Nat) : F)

def Gy : F :=
  ((0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5 : Nat) : F)

def G_nonsingular : W.Nonsingular Gx Gy := by native_decide

def G : W.Point := WeierstrassCurve.Affine.Point.some (x := Gx) (y := Gy) G_nonsingular

/-- ECDSA verification on secp256r1 / P-256 (FIPS 186-4 §6.4.2): the
generic `Ecdsa.verifyBytes` instantiated with the curve parameters
above. -/
def verifyBytes
    (pkX pkY : Array (BitVec 8))
    (sig : Array (BitVec 8))
    (msgHash : Array (BitVec 8)) : Bool :=
  Ecdsa.verifyBytes (W := W) orderN G pkX pkY sig msgHash

end Lampe.Crypto.Secp256r1
