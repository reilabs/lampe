import Lampe.Crypto.Ecdsa.Verify
import Lampe.Crypto.MathlibBridge
import Lampe.Crypto.Secp256k1.Prime
import Mathlib.Algebra.Field.ZMod

/-!
# secp256k1 — Bitcoin / Ethereum ECDSA curve

ECDSA verification on the curve `y² = x³ + 7` over the secp256k1
base field, operating on `WeierstrassCurve.Affine.Point`.

References:
- SEC 2 §2.4.1 (curve parameters)
- FIPS 186-4 §6.4.2 (ECDSA verification)
- RFC 6979 (deterministic test vector generation)
-/

namespace Lampe.Crypto.Secp256k1

open Lampe

abbrev F : Type := Fp Secp256k1.prime

def W : WeierstrassCurve.Affine F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 7 }

def orderN : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def Gx : F :=
  ((0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798 : Nat) : F)

def Gy : F :=
  ((0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 : Nat) : F)

def G_nonsingular : W.Nonsingular Gx Gy := by native_decide

def G : W.Point := WeierstrassCurve.Affine.Point.some (x := Gx) (y := Gy) G_nonsingular

/-- ECDSA verification on secp256k1 (FIPS 186-4 §6.4.2): the generic
`Ecdsa.verifyBytes` instantiated with the curve parameters above. -/
def verifyBytes
    (pkX pkY : Array (BitVec 8))
    (sig : Array (BitVec 8))
    (msgHash : Array (BitVec 8)) : Bool :=
  Ecdsa.verifyBytes (W := W) orderN G pkX pkY sig msgHash

end Lampe.Crypto.Secp256k1
