import Lampe.Tp

/-!
# Short Weierstrass curves — concrete reference for ECDSA

A computable Lean reference implementation that works for any
short-Weierstrass curve `y² = x³ + a·x + b` over a prime field Fp
with a generator subgroup of order n. Concrete curves (secp256k1,
secp256r1) just supply the parameters in their own modules.

The verification algorithm follows FIPS 186-4 §6.4.2. Coefficient `b`
is never used — point-on-curve checks happen outside Lampe — so the
structure omits it.

References:
- SECG, "SEC 2: Recommended Elliptic Curve Domain Parameters"
- FIPS 186-4 §6.4.2 (ECDSA verification)
-/

namespace Lampe.Crypto.Weierstrass

/-- Curve parameters: prime field, subgroup order, curve coefficient
`a`, and generator coordinates. We elide `b`: every operation in this
module is determined by `a`, `prime`, and `order`. -/
structure CurveParams where
  prime : Nat
  order : Nat
  a : Nat
  Gx : Nat
  Gy : Nat

namespace CurveParams

variable (C : CurveParams)

/-! ### Field arithmetic mod `C.prime` -/

@[inline] def fpAdd (a b : Nat) : Nat := (a + b) % C.prime
@[inline] def fpSub (a b : Nat) : Nat := (a + C.prime - b % C.prime) % C.prime
@[inline] def fpMul (a b : Nat) : Nat := (a * b) % C.prime

/-- Modular exponentiation in Fp. Loop bound 256 covers exponents up
to 2^256 - 1, which is more than enough for primes ≤ 256 bits used
by the curves we care about. -/
def fpPow (base exp : Nat) : Nat := Id.run do
  let mut result : Nat := 1
  let mut b : Nat := base % C.prime
  let mut e : Nat := exp
  for _ in [:256] do
    if e % 2 = 1 then
      result := (result * b) % C.prime
    e := e / 2
    b := (b * b) % C.prime
  return result

/-- Fermat-based modular inverse mod `C.prime` (assumed prime). Returns 0
when `a = 0`; callers must guard against that case. -/
@[inline] def fpInv (a : Nat) : Nat := C.fpPow a (C.prime - 2)

/-! ### Scalar arithmetic mod `C.order` -/

@[inline] def fnMul (a b : Nat) : Nat := (a * b) % C.order

/-- Modular exponentiation mod `C.order`. Same shape as `fpPow`. -/
def fnPow (base exp : Nat) : Nat := Id.run do
  let mut result : Nat := 1
  let mut b : Nat := base % C.order
  let mut e : Nat := exp
  for _ in [:256] do
    if e % 2 = 1 then
      result := (result * b) % C.order
    e := e / 2
    b := (b * b) % C.order
  return result

/-- Scalar-field inverse via Fermat (order n is prime). -/
@[inline] def fnInv (a : Nat) : Nat := C.fnPow a (C.order - 2)

end CurveParams

/-! ### Affine points -/

/-- An affine point on a Weierstrass curve, plus the point at infinity.
We do not store a curve-membership witness; callers are responsible
for supplying valid coordinates. -/
inductive Point where
  | infinity : Point
  | affine : Nat → Nat → Point
deriving DecidableEq, Repr

namespace Point

/-- Doubling in affine coordinates:
λ = (3x² + a) / (2y); xr = λ² - 2x; yr = λ(x - xr) - y.
Returns infinity when y = 0 (tangent is vertical). -/
def double (C : CurveParams) : Point → Point
  | .infinity => .infinity
  | .affine x y =>
    if y = 0 then .infinity
    else
      let num := C.fpAdd (C.fpMul 3 (C.fpMul x x)) C.a
      let den := C.fpInv (C.fpMul 2 y)
      let lam := C.fpMul num den
      let xr := C.fpSub (C.fpMul lam lam) (C.fpMul 2 x)
      let yr := C.fpSub (C.fpMul lam (C.fpSub x xr)) y
      .affine xr yr

/-- Affine point addition. Handles identity, additive inverses
(P + (-P) = ∞), and equal points (delegates to doubling). -/
def add (C : CurveParams) (P Q : Point) : Point :=
  match P, Q with
  | .infinity, _ => Q
  | _, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if x1 = x2 then
      if y1 = y2 then double C (.affine x1 y1)
      else .infinity
    else
      let lam := C.fpMul (C.fpSub y2 y1) (C.fpInv (C.fpSub x2 x1))
      let xr := C.fpSub (C.fpSub (C.fpMul lam lam) x1) x2
      let yr := C.fpSub (C.fpMul lam (C.fpSub x1 xr)) y1
      .affine xr yr

/-- Scalar multiplication via right-to-left double-and-add. Fixed 256
iterations covers every scalar that survives the mod-n reduction in
ECDSA (n < 2^256 for all curves we target). -/
def scalarMul (C : CurveParams) (k : Nat) (P : Point) : Point := Id.run do
  let mut acc : Point := .infinity
  let mut base : Point := P
  let mut e : Nat := k
  for _ in [:256] do
    if e % 2 = 1 then
      acc := add C acc base
    base := double C base
    e := e / 2
  return acc

end Point

/-! ### Byte ↔ scalar conversion -/

/-- Decode big-endian byte array to `Nat`. Output is the raw natural
value; callers reduce mod p or n as appropriate. -/
def bytesToNatBE (bs : Array (BitVec 8)) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-! ### ECDSA verification

Algorithm (FIPS 186-4 §6.4.2):
  1. Parse r, s from a 64-byte signature (r = first 32 bytes BE,
     s = last 32 bytes BE). Reject if r or s is 0 or ≥ n.
  2. Parse public key Q = (Qx, Qy) and message hash z.
  3. Compute s⁻¹ mod n; u₁ = z·s⁻¹ mod n; u₂ = r·s⁻¹ mod n.
  4. R = u₁·G + u₂·Q.
  5. Accept iff R ≠ ∞ ∧ (Rx mod n) = r.

We assume Q lies on the curve — Noir's foreign-call interface
already enforces this when accepting a public key. -/

def verifyBytes (C : CurveParams)
    (pkX pkY : Array (BitVec 8))
    (sig : Array (BitVec 8))
    (msgHash : Array (BitVec 8)) : Bool := Id.run do
  -- Parse signature
  let r := bytesToNatBE (sig.extract 0 32)
  let s := bytesToNatBE (sig.extract 32 64)
  if r = 0 then return false
  if r ≥ C.order then return false
  if s = 0 then return false
  if s ≥ C.order then return false
  -- Parse message hash and public key
  let z := bytesToNatBE msgHash
  let qx := bytesToNatBE pkX
  let qy := bytesToNatBE pkY
  let zRed := z % C.order
  let sInv := C.fnInv s
  let u1 := C.fnMul zRed sInv
  let u2 := C.fnMul r sInv
  let R := Point.add C
             (Point.scalarMul C u1 (.affine C.Gx C.Gy))
             (Point.scalarMul C u2 (.affine qx qy))
  match R with
  | .infinity => return false
  | .affine xr _ => return (xr % C.order) = r

end Lampe.Crypto.Weierstrass
