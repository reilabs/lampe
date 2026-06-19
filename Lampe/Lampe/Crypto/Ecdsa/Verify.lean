import Lampe.Crypto.MathlibBridge
import Lampe.Data.Field
import Mathlib.Algebra.Field.ZMod

/-!
# ECDSA signature verification — generic implementation

The curve-independent core of ECDSA verification (FIPS 186-4 §6.4.2),
parameterized over the curve, its group order, and the generator
point. `Lampe/Crypto/Secp256k1.lean` and `Secp256r1.lean` instantiate
it with their respective SEC 2 / FIPS 186-4 parameters.

Scalars are at most 256 bits on both supported curves, which is what
the iteration bounds in `orderPow` and (via `scalarMul`) the
double-and-add loops rely on.
-/

namespace Lampe.Crypto.Ecdsa

/-- Interpret a byte array as a big-endian natural number. -/
def bytesToNatBE (bs : Array (BitVec 8)) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Modular exponentiation `base ^ exp % orderN` by square-and-multiply
over the low 256 bits of `exp` (the group orders we instantiate with
are 256-bit). -/
def orderPow (orderN base exp : Nat) : Nat := Id.run do
  let mut result : Nat := 1
  let mut b : Nat := base % orderN
  let mut e : Nat := exp
  for _ in [:256] do
    if e % 2 = 1 then
      result := (result * b) % orderN
    e := e / 2
    b := (b * b) % orderN
  return result

/-- Modular inverse modulo the prime group order `orderN`, via
Fermat's little theorem: `a⁻¹ = a^(orderN - 2)`. -/
@[inline] def orderInv (orderN a : Nat) : Nat := orderPow orderN a (orderN - 2)

/-- ECDSA verification (FIPS 186-4 §6.4.2), generic over the curve
`W`, its (256-bit, prime) group order `orderN`, and the generator
`G`. Returns `false` on malformed `r`/`s`, an off-curve public key, or
x-coordinate mismatch; `true` iff the signature is valid. -/
def verifyBytes {P : Prime} {W : WeierstrassCurve.Affine (Fp P)}
    (orderN : Nat) (G : W.Point)
    (pkX pkY : Array (BitVec 8))
    (sig : Array (BitVec 8))
    (msgHash : Array (BitVec 8)) : Bool := Id.run do
  let r := bytesToNatBE (sig.extract 0 32)
  let s := bytesToNatBE (sig.extract 32 64)
  if r = 0 then return false
  if r ≥ orderN then return false
  if s = 0 then return false
  if s ≥ orderN then return false
  let qx : Fp P := ((bytesToNatBE pkX : Nat) : Fp P)
  let qy : Fp P := ((bytesToNatBE pkY : Nat) : Fp P)
  if hQ : W.Nonsingular qx qy then
    let z := bytesToNatBE msgHash
    let zRed := z % orderN
    let sInv := orderInv orderN s
    let u1 := (zRed * sInv) % orderN
    let u2 := (r * sInv) % orderN
    let Q : W.Point := WeierstrassCurve.Affine.Point.some (x := qx) (y := qy) hQ
    let R : W.Point := scalarMul G u1 + scalarMul Q u2
    match R with
    | .zero => return false
    | @WeierstrassCurve.Affine.Point.some _ _ _ xr _ _ => return (xr.val % orderN) = r
  else
    return false

end Lampe.Crypto.Ecdsa
