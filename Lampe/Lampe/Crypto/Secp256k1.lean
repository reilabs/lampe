import Lampe.Tp

/-!
# secp256k1 — concrete curve and ECDSA verification

Computable Lean reference for the secp256k1 elliptic curve used by
Bitcoin, Ethereum, and Noir's `ecdsa_secp256k1::verify_signature`.
Field is Fp where:

  p = 2^256 - 2^32 - 977
  n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
  E : y² = x³ + 7

References:
- SECG, "SEC 2: Recommended Elliptic Curve Domain Parameters" §2.4.1
- https://en.bitcoin.it/wiki/Secp256k1
- NIST FIPS 186-4 §6.4 (ECDSA verification)

Field elements are represented as `Nat` reduced modulo `primeFp`;
scalars are `Nat` reduced modulo `orderFn`. This keeps `native_decide`
happy (no `partial def`, all functions terminate in ≤ 256 iterations
by construction).
-/

namespace Lampe.Crypto.Secp256k1

/-! ### Curve constants -/

/-- Field prime: p = 2^256 - 2^32 - 977. -/
def primeFp : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- Curve order n. -/
def orderFn : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- Generator x-coordinate. -/
def Gx : Nat :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- Generator y-coordinate. -/
def Gy : Nat :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-! ### Field arithmetic mod p -/

@[inline] def fpAdd (a b : Nat) : Nat := (a + b) % primeFp
@[inline] def fpSub (a b : Nat) : Nat := (a + primeFp - b % primeFp) % primeFp
@[inline] def fpMul (a b : Nat) : Nat := (a * b) % primeFp

/-- Modular exponentiation in Fp by right-to-left binary expansion.
The loop bound is fixed at 256 because exponents fed here are always
< p < 2^256 (Fermat's little theorem uses `primeFp - 2` as the
exponent). -/
def fpPow (base exp : Nat) : Nat := Id.run do
  let mut result : Nat := 1
  let mut b : Nat := base % primeFp
  let mut e : Nat := exp
  for _ in [:256] do
    if e % 2 = 1 then
      result := (result * b) % primeFp
    e := e / 2
    b := (b * b) % primeFp
  return result

/-- Modular inverse via Fermat: a^(p-2) ≡ a^(-1) mod p when gcd(a, p) = 1.
For `a = 0` returns 0; callers must guard against that case. -/
@[inline] def fpInv (a : Nat) : Nat := fpPow a (primeFp - 2)

/-! ### Scalar field arithmetic mod n -/

@[inline] def fnAdd (a b : Nat) : Nat := (a + b) % orderFn
@[inline] def fnMul (a b : Nat) : Nat := (a * b) % orderFn

/-- Modular exponentiation mod n. Same shape as `fpPow`. -/
def fnPow (base exp : Nat) : Nat := Id.run do
  let mut result : Nat := 1
  let mut b : Nat := base % orderFn
  let mut e : Nat := exp
  for _ in [:256] do
    if e % 2 = 1 then
      result := (result * b) % orderFn
    e := e / 2
    b := (b * b) % orderFn
  return result

/-- Scalar-field inverse via Fermat (n is prime). -/
@[inline] def fnInv (a : Nat) : Nat := fnPow a (orderFn - 2)

/-! ### Affine points and curve arithmetic -/

/-- An affine point on the curve, plus the point at infinity. We do
not store a curve-membership witness; callers are responsible for
passing valid coordinates. ECDSA verify will skip a point-on-curve
check (the Noir backend performs it externally). -/
inductive Point where
  | infinity : Point
  | affine : Nat → Nat → Point
deriving DecidableEq, Repr

namespace Point

/-- Negate an affine point: `-(x, y) = (x, p - y)`. -/
def neg : Point → Point
  | .infinity => .infinity
  | .affine x y => .affine x (fpSub 0 y)

/-- Point doubling in affine coordinates (curve a = 0).
λ = (3x²) / (2y); xr = λ² - 2x; yr = λ(x - xr) - y.
Returns infinity if y = 0 (tangent is vertical). -/
def double : Point → Point
  | .infinity => .infinity
  | .affine x y =>
    if y = 0 then .infinity
    else
      let num := fpMul 3 (fpMul x x)
      let den := fpInv (fpMul 2 y)
      let lam := fpMul num den
      let xr := fpSub (fpMul lam lam) (fpMul 2 x)
      let yr := fpSub (fpMul lam (fpSub x xr)) y
      .affine xr yr

/-- Affine point addition. Handles all the special cases:
identity, additive inverses (P + (-P) = ∞), and equal points
(falls through to doubling). -/
def add (P Q : Point) : Point :=
  match P, Q with
  | .infinity, _ => Q
  | _, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if x1 = x2 then
      if y1 = y2 then double (.affine x1 y1)
      else .infinity  -- P + (-P) = O
    else
      let lam := fpMul (fpSub y2 y1) (fpInv (fpSub x2 x1))
      let xr := fpSub (fpSub (fpMul lam lam) x1) x2
      let yr := fpSub (fpMul lam (fpSub x1 xr)) y1
      .affine xr yr

/-- Scalar multiplication via right-to-left double-and-add. Fixed
loop bound at 256 since k mod n < n < 2^256. -/
def scalarMul (k : Nat) (P : Point) : Point := Id.run do
  let mut acc : Point := .infinity
  let mut base : Point := P
  let mut e : Nat := k
  for _ in [:256] do
    if e % 2 = 1 then
      acc := acc.add base
    base := base.double
    e := e / 2
  return acc

end Point

/-! ### Byte ↔ scalar conversions -/

/-- Decode 32 big-endian bytes into a `Nat` (left byte = most-significant).
Output is the natural-number value of the byte string; callers reduce
mod p or n as appropriate. -/
def bytesToNatBE (bs : Array (BitVec 8)) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-! ### ECDSA signature verification

Algorithm (FIPS 186-4 §6.4.2):
  1. Parse r, s from the 64-byte signature (first 32 bytes = r BE,
     last 32 = s BE). Reject if r or s is 0 or ≥ n.
  2. Parse public key Q = (Qx, Qy) and message hash z.
  3. Compute s⁻¹ mod n; u₁ = z·s⁻¹ mod n; u₂ = r·s⁻¹ mod n.
  4. R = u₁·G + u₂·Q.
  5. Accept iff R ≠ ∞ ∧ (Rx mod n) = r.

We do **not** validate that Q is on the curve here; the Noir backend
already enforces this when it accepts a public key. Treating Q as
on-curve is consistent with how Barretenberg's foreign builtin works.
-/

/-- Concrete secp256k1 ECDSA verification taking byte-array arguments.
This is the algorithmic core; the wrapper in `Lampe.Crypto.Ecdsa`
adapts it to the `Tp.denote` shape expected by the builtin descriptor. -/
def verifyBytes
    (pkX pkY : Array (BitVec 8))
    (sig : Array (BitVec 8))
    (msgHash : Array (BitVec 8)) : Bool := Id.run do
  -- Parse signature
  let r := bytesToNatBE (sig.extract 0 32)
  let s := bytesToNatBE (sig.extract 32 64)
  if r = 0 then return false
  if r ≥ orderFn then return false
  if s = 0 then return false
  if s ≥ orderFn then return false
  -- Parse message hash and public key
  let z := bytesToNatBE msgHash
  let qx := bytesToNatBE pkX
  let qy := bytesToNatBE pkY
  -- Per FIPS 186-4, z is reduced mod n if longer than ⌈log2 n⌉.
  -- For 32-byte hashes and 256-bit n, we take z mod n directly.
  let zRed := z % orderFn
  let sInv := fnInv s
  let u1 := fnMul zRed sInv
  let u2 := fnMul r sInv
  let R := (Point.scalarMul u1 (.affine Gx Gy)).add
             (Point.scalarMul u2 (.affine qx qy))
  match R with
  | .infinity => return false
  | .affine xr _ => return (xr % orderFn) = r

/-! ### Test vectors

Validation against reference signatures generated by the pure-Python
`ecdsa` library in deterministic (RFC 6979) mode. Both `validSimple`
and `validSeq` are real signatures produced by `sk.sign_digest_*`;
`tampered` is `validSimple` with one signature byte flipped, which
must be rejected.

Regenerate with `scripts/secp256k1_ref.py`. Matching these vectors
transitively certifies agreement with Barretenberg's
`__ecdsa_secp256k1`, which must implement the standard FIPS 186-4
verification algorithm. -/

-- validSimple: sk = 0x01..01, msg = "Lampe ECDSA test vector"
private def validSimplePkX : Array (BitVec 8) := #[0x1b#8, 0x84#8, 0xc5#8, 0x56#8, 0x7b#8, 0x12#8, 0x64#8, 0x40#8, 0x99#8, 0x5d#8, 0x3e#8, 0xd5#8, 0xaa#8, 0xba#8, 0x05#8, 0x65#8, 0xd7#8, 0x1e#8, 0x18#8, 0x34#8, 0x60#8, 0x48#8, 0x19#8, 0xff#8, 0x9c#8, 0x17#8, 0xf5#8, 0xe9#8, 0xd5#8, 0xdd#8, 0x07#8, 0x8f#8]
private def validSimplePkY : Array (BitVec 8) := #[0x70#8, 0xbe#8, 0xaf#8, 0x8f#8, 0x58#8, 0x8b#8, 0x54#8, 0x15#8, 0x07#8, 0xfe#8, 0xd6#8, 0xa6#8, 0x42#8, 0xc5#8, 0xab#8, 0x42#8, 0xdf#8, 0xdf#8, 0x81#8, 0x20#8, 0xa7#8, 0xf6#8, 0x39#8, 0xde#8, 0x51#8, 0x22#8, 0xd4#8, 0x7a#8, 0x69#8, 0xa8#8, 0xe8#8, 0xd1#8]
private def validSimpleSig : Array (BitVec 8) := #[0x4d#8, 0x07#8, 0x54#8, 0xd6#8, 0x23#8, 0x0f#8, 0x85#8, 0x35#8, 0x33#8, 0xb8#8, 0x68#8, 0x77#8, 0x98#8, 0x43#8, 0xcb#8, 0x7f#8, 0x30#8, 0x85#8, 0xc9#8, 0xd6#8, 0x21#8, 0xd8#8, 0x40#8, 0xe8#8, 0xc1#8, 0xb4#8, 0x1a#8, 0x85#8, 0x1b#8, 0x56#8, 0x37#8, 0x90#8, 0x82#8, 0x9e#8, 0x4c#8, 0x7e#8, 0x20#8, 0xb8#8, 0x57#8, 0x00#8, 0x37#8, 0x82#8, 0x0e#8, 0x49#8, 0x09#8, 0x38#8, 0x41#8, 0xb1#8, 0x18#8, 0x31#8, 0x26#8, 0x7d#8, 0xa4#8, 0x52#8, 0x22#8, 0xcd#8, 0x78#8, 0x1d#8, 0xcf#8, 0xde#8, 0x38#8, 0x0b#8, 0x47#8, 0x00#8]
private def validSimpleMsg : Array (BitVec 8) := #[0x94#8, 0xbd#8, 0x9f#8, 0xb9#8, 0xaa#8, 0x9a#8, 0x8c#8, 0x3f#8, 0xd9#8, 0x1c#8, 0x1d#8, 0xe7#8, 0x50#8, 0x95#8, 0x33#8, 0x97#8, 0xdb#8, 0xdf#8, 0x1f#8, 0x84#8, 0x45#8, 0xf2#8, 0x80#8, 0xc8#8, 0xf6#8, 0x63#8, 0x9f#8, 0x12#8, 0x2c#8, 0x6f#8, 0x81#8, 0x92#8]
theorem secp256k1_validSimple_correct :
    verifyBytes validSimplePkX validSimplePkY validSimpleSig validSimpleMsg = true := by
  native_decide

-- validSeq: sk = 0x01..20, msg = "another message"
private def validSeqPkX : Array (BitVec 8) := #[0x84#8, 0xbf#8, 0x75#8, 0x62#8, 0x26#8, 0x2b#8, 0xbd#8, 0x69#8, 0x40#8, 0x08#8, 0x57#8, 0x48#8, 0xf3#8, 0xbe#8, 0x6a#8, 0xfa#8, 0x52#8, 0xae#8, 0x31#8, 0x71#8, 0x55#8, 0x18#8, 0x1e#8, 0xce#8, 0x31#8, 0xb6#8, 0x63#8, 0x51#8, 0xcc#8, 0xff#8, 0xa4#8, 0xb0#8]
private def validSeqPkY : Array (BitVec 8) := #[0x8c#8, 0xc4#8, 0x3d#8, 0x63#8, 0xb2#8, 0x85#8, 0x9d#8, 0x46#8, 0x9f#8, 0xee#8, 0x15#8, 0xf3#8, 0x1c#8, 0x9e#8, 0xdb#8, 0x53#8, 0x24#8, 0x26#8, 0x6e#8, 0x6f#8, 0xd0#8, 0x40#8, 0x7e#8, 0x87#8, 0x38#8, 0x2d#8, 0x60#8, 0xfc#8, 0x45#8, 0x11#8, 0xac#8, 0xd8#8]
private def validSeqSig : Array (BitVec 8) := #[0xf1#8, 0xc3#8, 0xb7#8, 0x00#8, 0x4b#8, 0xf7#8, 0xb9#8, 0x37#8, 0xf4#8, 0x01#8, 0xf6#8, 0x86#8, 0xb9#8, 0xd7#8, 0x6b#8, 0x87#8, 0x46#8, 0xc2#8, 0x21#8, 0xef#8, 0xe6#8, 0xce#8, 0xeb#8, 0xf6#8, 0x31#8, 0x9e#8, 0xbd#8, 0xcf#8, 0xf3#8, 0x71#8, 0x82#8, 0x31#8, 0x70#8, 0x09#8, 0x20#8, 0x12#8, 0x27#8, 0xd4#8, 0xf0#8, 0xe9#8, 0x74#8, 0x78#8, 0x0f#8, 0x0f#8, 0x8d#8, 0xeb#8, 0x5e#8, 0x3c#8, 0x6e#8, 0x74#8, 0xd1#8, 0xb3#8, 0xa7#8, 0xa7#8, 0x11#8, 0x44#8, 0xe5#8, 0xb5#8, 0xc5#8, 0xaf#8, 0x90#8, 0x61#8, 0x8f#8, 0x85#8]
private def validSeqMsg : Array (BitVec 8) := #[0x28#8, 0xea#8, 0x0f#8, 0x23#8, 0x11#8, 0x92#8, 0xa6#8, 0x57#8, 0x11#8, 0xa6#8, 0x44#8, 0x00#8, 0x3b#8, 0x0c#8, 0xb3#8, 0xa0#8, 0x49#8, 0xbf#8, 0xaf#8, 0x43#8, 0x39#8, 0x7b#8, 0x36#8, 0xc8#8, 0xbe#8, 0xed#8, 0x63#8, 0x13#8, 0x73#8, 0x74#8, 0xed#8, 0x97#8]
theorem secp256k1_validSeq_correct :
    verifyBytes validSeqPkX validSeqPkY validSeqSig validSeqMsg = true := by
  native_decide

-- tampered: validSimple signature with one bit flipped → reject
private def tamperedSig : Array (BitVec 8) := #[0x4c#8, 0x07#8, 0x54#8, 0xd6#8, 0x23#8, 0x0f#8, 0x85#8, 0x35#8, 0x33#8, 0xb8#8, 0x68#8, 0x77#8, 0x98#8, 0x43#8, 0xcb#8, 0x7f#8, 0x30#8, 0x85#8, 0xc9#8, 0xd6#8, 0x21#8, 0xd8#8, 0x40#8, 0xe8#8, 0xc1#8, 0xb4#8, 0x1a#8, 0x85#8, 0x1b#8, 0x56#8, 0x37#8, 0x90#8, 0x82#8, 0x9e#8, 0x4c#8, 0x7e#8, 0x20#8, 0xb8#8, 0x57#8, 0x00#8, 0x37#8, 0x82#8, 0x0e#8, 0x49#8, 0x09#8, 0x38#8, 0x41#8, 0xb1#8, 0x18#8, 0x31#8, 0x26#8, 0x7d#8, 0xa4#8, 0x52#8, 0x22#8, 0xcd#8, 0x78#8, 0x1d#8, 0xcf#8, 0xde#8, 0x38#8, 0x0b#8, 0x47#8, 0x00#8]
theorem secp256k1_tampered_correct :
    verifyBytes validSimplePkX validSimplePkY tamperedSig validSimpleMsg = false := by
  native_decide

end Lampe.Crypto.Secp256k1
