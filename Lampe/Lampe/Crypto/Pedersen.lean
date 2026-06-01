import Lampe.Tp
import Lampe.Crypto.EmbeddedCurve
import Lampe.Crypto.Blake3
import Lampe.Crypto.Bn254
import Lampe.Crypto.Sqrt

/-!
# Pedersen generator derivation — concrete model

This module formalizes Noir's `derive_pedersen_generators` foreign
builtin (stdlib `std::hash::derive_generators`). The Noir compiler
dispatches this builtin to Barretenberg's `derive_generators`
routine, which deterministically hashes a domain-separator byte
string together with an index to produce a stream of points on
Grumpkin (`y^2 = x^3 - 17`) via a hash-to-curve construction
(BLAKE3 + try-and-increment).

The implementation transcribes Barretenberg's
`affine_element::hash_to_curve` (file
`barretenberg/cpp/src/barretenberg/ecc/groups/affine_element_impl.hpp`)
and the surrounding `derive_generators` wrapper. The generator
returned by `pedersenGeneratorPoint p domain index` is:

1. Build a 64-byte preimage `BLAKE3(domain) || BE32(index) || zeros(28)`.
2. For `attempt = 0, 1, …` (bounded by 256):
   - Compute `hash_hi = BLAKE3(preimage ‖ attempt ‖ 0)` and
     `hash_lo = BLAKE3(preimage ‖ attempt ‖ 1)`.
   - Read both as big-endian 256-bit integers, concatenate as
     `n_hi · 2^256 + n_lo`, and reduce modulo `p` to obtain
     `x : Fp p`.
   - Take the parity bit from the top bit of `hash_hi[0]`.
   - Compute `yy = x^3 + curveB` (curveB = -17 for Grumpkin) and
     attempt `sqrt yy` via Tonelli-Shanks.
   - On success, pick the candidate root whose parity matches the
     parity bit; verify via `curvePoint?` that the resulting
     `(x, y, false)` lies on the affine curve. If yes, return the
     corresponding Mathlib point.

The Tonelli-Shanks square root (`Lampe.Crypto.Sqrt.sqrt`) is only
defined when `p` is the BN254 scalar-field prime. For other primes
the function returns the point at infinity (a meaningless
placeholder; downstream specs always instantiate `p` to the BN254
scalar prime). This is encoded via a dependent-`if` on
`p.natVal = r_scalar`, with the `Lampe.Crypto.Bn254.Prime p` instance derived
from the equality witness on the success branch.
-/

namespace Lampe.Crypto.Pedersen

open Lampe.Crypto.EmbeddedCurve
open Lampe.Crypto.Blake3
open Lampe.Crypto.Bn254 (r_scalar)
open Lampe.Crypto.Sqrt

/-! ### Byte-buffer plumbing -/

/-- Read the first 32 bytes of `bytes` as a big-endian 256-bit
unsigned integer. Positions past the array bound are treated as
zero. -/
private def bytesToBigEndianU256 (bytes : Array (BitVec 8)) : Nat := Id.run do
  let mut acc : Nat := 0
  for i in [:32] do
    let b : Nat := (bytes.getD i 0).toNat
    acc := acc * 256 + b
  return acc

private def domainListToBytes (domain : List Nat) : Array (BitVec 8) :=
  (domain.map (fun n => BitVec.ofNat 8 n)).toArray

/-- Build the 64-byte preimage `BLAKE3(domain) ‖ BE32(index) ‖ 0×28`
that seeds the per-index hash-to-curve loop. -/
private def makePreimage (domain : List Nat) (index : Nat) : Array (BitVec 8) := Id.run do
  let domainBytes := domainListToBytes domain
  let domainHash := blake3HashBytes domainBytes
  let mut preimage : Array (BitVec 8) := Array.replicate 64 0
  -- First 32 bytes: BLAKE3(domain).
  for i in [:32] do
    preimage := preimage.set! i (domainHash.getD i 0)
  -- Bytes [32, 36): big-endian u32 encoding of `index`.
  preimage := preimage.set! 32 (BitVec.ofNat 8 ((index >>> 24) &&& 0xff))
  preimage := preimage.set! 33 (BitVec.ofNat 8 ((index >>> 16) &&& 0xff))
  preimage := preimage.set! 34 (BitVec.ofNat 8 ((index >>>  8) &&& 0xff))
  preimage := preimage.set! 35 (BitVec.ofNat 8 (index           &&& 0xff))
  -- Bytes [36, 64) are already zero from `Array.replicate`.
  return preimage

/-- Append the attempt counter and a 1-byte tag (0 for the high half,
1 for the low half) to the 64-byte preimage to produce the 66-byte
BLAKE3 input for one hash-to-curve attempt. -/
private def makeAttemptSeed (preimage : Array (BitVec 8))
    (count tag : Nat) : Array (BitVec 8) :=
  preimage.push (BitVec.ofNat 8 count) |>.push (BitVec.ofNat 8 tag)

/-! ### Hash-to-curve inner loop -/

/-- Try to lift `(x, y)` to a Mathlib affine point with the requested
parity, retrying with `-y` if needed. Returns `none` when the
candidate `(x, ±y)` fails the on-curve check. -/
private def liftWithParity {p : Prime} (x y : Fp p) (signBit : Bool) :
    Option ((affineCurve p).Point) :=
  let y_final : Fp p :=
    if (y.val % 2 == 1) == signBit then y else (-y)
  curvePoint? (mkPoint x y_final false)

/--
Single hash-to-curve attempt for `(preimage, attempt)`. Builds the
two BLAKE3 outputs, derives an `x` coordinate, attempts to compute
`y = sqrt(x^3 + B)`, and lifts to a Mathlib point with the parity
encoded in the high bit of `hash_hi[0]`.
-/
private def hashToCurveAttempt {p : Prime} [Lampe.Crypto.Bn254.Prime p]
    (preimage : Array (BitVec 8)) (attempt : Nat) :
    Option ((affineCurve p).Point) :=
  let seedHi := makeAttemptSeed preimage attempt 0
  let seedLo := makeAttemptSeed preimage attempt 1
  let hashHi := blake3HashBytes seedHi
  let hashLo := blake3HashBytes seedLo
  let nHi : Nat := bytesToBigEndianU256 hashHi
  let nLo : Nat := bytesToBigEndianU256 hashLo
  let combined : Nat := nHi * (2 ^ 256) + nLo
  let x : Fp p := (combined : Nat)
  let signBit : Bool := (hashHi.getD 0 0).toNat >>> 7 == 1
  let yy : Fp p := x * x * x + curveB
  let (found, yCand) := sqrt yy
  if found then liftWithParity x yCand signBit else none

/-- Hash-to-curve loop, bounded by 256 attempts. The probability that
a uniformly random `x` is the x-coordinate of a Grumpkin point is
≈ 1/2, so the expected number of iterations is 2; 256 attempts is
astronomically generous. -/
private def hashToCurve {p : Prime} [Lampe.Crypto.Bn254.Prime p]
    (preimage : Array (BitVec 8)) : (affineCurve p).Point := Id.run do
  for attempt in [:256] do
    match hashToCurveAttempt preimage attempt with
    | some pt => return pt
    | none => continue
  -- Statistically unreachable: the probability of failing 256 times
  -- is ≈ 2^(-256). Fall through with the identity element.
  return 0

/-- Concrete BN254-scalar generator builder. Combines `makePreimage`
with the bounded `hashToCurve` loop. -/
def pedersenGenerator {p : Prime} [Lampe.Crypto.Bn254.Prime p]
    (domain : List Nat) (index : Nat) : (affineCurve p).Point :=
  hashToCurve (makePreimage domain index)

/-! ### Public per-index generator -/

/--
Per-index Pedersen generator derivation.

When `p` is the BN254 scalar prime, this runs Barretenberg's
hash-to-curve algorithm (BLAKE3 + Tonelli-Shanks) and returns the
encoded Grumpkin generator. For any other prime, the function
returns the point at infinity; downstream specs only instantiate
`p` at BN254, so the non-BN254 branch is never observed.
-/
def pedersenGeneratorPoint (p : Prime) (domain : List Nat) (index : Nat) : Point p :=
  if h : p.natVal = r_scalar then
    haveI : Lampe.Crypto.Bn254.Prime p := ⟨h⟩
    encodeCurvePoint (pedersenGenerator (p := p) domain index)
  else
    pointAtInfinity

/-- Bridge: `pedersenGeneratorPoint` is the encoding of `pedersenGenerator`
under any `Lampe.Crypto.Bn254.Prime p` instance. Used by stdlib specs to discharge the
`encodeCurvePoint (Ps.get i) = pedersenGeneratorPoint …` obligation that
`multi_scalar_mul_spec` expects. -/
@[simp] theorem pedersenGeneratorPoint_eq {p : Prime} [Lampe.Crypto.Bn254.Prime p]
    (domain : List Nat) (index : Nat) :
    pedersenGeneratorPoint p domain index =
      encodeCurvePoint (pedersenGenerator (p := p) domain index) := by
  unfold pedersenGeneratorPoint
  have h : p.natVal = r_scalar := Lampe.Crypto.Bn254.Prime.natVal_eq_r_scalar
  rw [dif_pos h]

/-- Build a length-`N` vector of generators starting at `startIndex`. -/
def derivePedersenGeneratorsList (p : Prime) (domain : List Nat) (startIndex N : Nat) :
    List (Point p) :=
  (List.range N).map (fun i => pedersenGeneratorPoint p domain (startIndex + i))

theorem derivePedersenGeneratorsList_length (p : Prime) (domain : List Nat)
    (startIndex N : Nat) :
    (derivePedersenGeneratorsList p domain startIndex N).length = N := by
  simp [derivePedersenGeneratorsList]

/-- The semantic model used by the builtin descriptor: a `List.Vector`
of exactly `N` generators. -/
def derivePedersenGenerators (p : Prime) (domain : List Nat) (startIndex N : Nat) :
    List.Vector (Point p) N :=
  ⟨derivePedersenGeneratorsList p domain startIndex N,
    derivePedersenGeneratorsList_length p domain startIndex N⟩

@[simp] theorem derivePedersenGenerators_get (p : Prime) (domain : List Nat)
    (startIndex N : Nat) (i : Fin N) :
    (derivePedersenGenerators p domain startIndex N).get i =
      pedersenGeneratorPoint p domain (startIndex + i.val) := by
  simp [derivePedersenGenerators, derivePedersenGeneratorsList,
    List.Vector.get, List.get_eq_getElem]

@[simp] theorem derivePedersenGenerators_toList (p : Prime) (domain : List Nat)
    (startIndex N : Nat) :
    (derivePedersenGenerators p domain startIndex N).toList =
      derivePedersenGeneratorsList p domain startIndex N := rfl

/-- Convert a length-`M` byte vector to the `List Nat` used as the
opaque domain-separator key. -/
def bytesToList {p M} (bs : Tp.denote p ((Tp.u 8).array M)) : List Nat :=
  bs.toList.map (fun b => b.toNat)

end Lampe.Crypto.Pedersen
