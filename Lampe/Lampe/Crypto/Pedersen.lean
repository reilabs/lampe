import Lampe.Tp
import Lampe.Crypto.EmbeddedCurve
import Lampe.Crypto.Blake3
import Lampe.Crypto.Bn254
import Lampe.Crypto.Bn254.Sqrt

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

The Tonelli-Shanks square root (`Lampe.Crypto.Bn254.Sqrt.sqrt`) is only
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
open Lampe.Crypto.Bn254.Sqrt

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

private def domainListToBytes (domain : List (BitVec 8)) : Array (BitVec 8) :=
  domain.toArray

/-- Build the 64-byte preimage `BLAKE3(domain) ‖ BE32(index) ‖ 0×28`
that seeds the per-index hash-to-curve loop. -/
private def makePreimage (domain : List (BitVec 8)) (index : Nat) : Array (BitVec 8) := Id.run do
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
  curvePoint? (mkPoint x y_final)

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
  match sqrt yy with
  | some yCand => liftWithParity x yCand signBit
  | none => none

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
    (domain : List (BitVec 8)) (index : Nat) : (affineCurve p).Point :=
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
def pedersenGeneratorPoint (p : Prime) (domain : List (BitVec 8)) (index : Nat) : Point p :=
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
    (domain : List (BitVec 8)) (index : Nat) :
    pedersenGeneratorPoint p domain index =
      encodeCurvePoint (pedersenGenerator (p := p) domain index) := by
  unfold pedersenGeneratorPoint
  have h : p.natVal = r_scalar := Lampe.Crypto.Bn254.Prime.natVal_eq_r_scalar
  rw [dif_pos h]

/-- Build a length-`N` vector of generators starting at `startIndex`. -/
def derivePedersenGeneratorsList (p : Prime) (domain : List (BitVec 8)) (startIndex N : Nat) :
    List (Point p) :=
  (List.range N).map (fun i => pedersenGeneratorPoint p domain (startIndex + i))

theorem derivePedersenGeneratorsList_length (p : Prime) (domain : List (BitVec 8))
    (startIndex N : Nat) :
    (derivePedersenGeneratorsList p domain startIndex N).length = N := by
  simp [derivePedersenGeneratorsList]

/-- The semantic model used by the builtin descriptor: a `List.Vector`
of exactly `N` generators. -/
def derivePedersenGenerators (p : Prime) (domain : List (BitVec 8)) (startIndex N : Nat) :
    List.Vector (Point p) N :=
  ⟨derivePedersenGeneratorsList p domain startIndex N,
    derivePedersenGeneratorsList_length p domain startIndex N⟩

@[simp] theorem derivePedersenGenerators_get (p : Prime) (domain : List (BitVec 8))
    (startIndex N : Nat) (i : Fin N) :
    (derivePedersenGenerators p domain startIndex N).get i =
      pedersenGeneratorPoint p domain (startIndex + i.val) := by
  simp [derivePedersenGenerators, derivePedersenGeneratorsList,
    List.Vector.get, List.get_eq_getElem]

@[simp] theorem derivePedersenGenerators_toList (p : Prime) (domain : List (BitVec 8))
    (startIndex N : Nat) :
    (derivePedersenGenerators p domain startIndex N).toList =
      derivePedersenGeneratorsList p domain startIndex N := rfl

/-- Bridging lemma: a generator vector derived by
`derivePedersenGenerators` is the `encodeCurvePoint`-image of any
Mathlib point vector `Ps` that agrees with `pedersenGeneratorPoint`
index-wise. Used by stdlib specs to discharge the encoded-points
hypothesis that `multi_scalar_mul_spec` expects. -/
theorem derivePedersenGenerators_h_enc {p : Prime} {n : Nat}
    {domain : List (BitVec 8)} {start : Nat}
    {Ps : List.Vector (affineCurve p).Point n}
    (h_gen : ∀ i,
      encodeCurvePoint (Ps.get i) =
        pedersenGeneratorPoint p domain (start + i.val)) :
    (derivePedersenGenerators p domain start n).toList =
      Ps.toList.map encodeCurvePoint := by
  rw [← List.Vector.toList_map]
  apply congrArg List.Vector.toList
  apply List.Vector.ext
  intro i
  rw [derivePedersenGenerators_get,
    List.Vector.get_map, ← h_gen i]

/-! ### Pure Pedersen commitment and hash -/

/-- ASCII byte vector for the literal `"DEFAULT_DOMAIN_SEPARATOR"`
(24 bytes). Used by `pedersen_commitment_with_separator` and
`pedersen_hash_with_separator`. -/
def defaultDomainBytes : List (BitVec 8) :=
  [68, 69, 70, 65, 85, 76, 84, 95,    -- "DEFAULT_"
   68, 79, 77, 65, 73, 78, 95,         -- "DOMAIN_"
   83, 69, 80, 65, 82, 65, 84, 79, 82] -- "SEPARATOR"

/-- ASCII byte vector for the literal `"pedersen_hash_length"`
(20 bytes). Used by `pedersen_hash_with_separator` for the
length-slot generator. -/
def pedersenHashLengthBytes : List (BitVec 8) :=
  [112, 101, 100, 101, 114, 115, 101, 110, 95,  -- "pedersen_"
   104, 97, 115, 104, 95,                       -- "hash_"
   108, 101, 110, 103, 116, 104]                 -- "length"

/-- Pure Pedersen commitment: canonically decompose each input field
element into limbs, scale the per-index generator
`pedersenGenerator domain (separator + i)` by the limb value, sum, and
encode the resulting curve point. This is the exact closed form that
the stdlib `pedersen_commitment*_spec_canonical` theorems guarantee
for Noir's `std::hash::pedersen_commitment_with_separator`. -/
def pedersenCommitment (p : Prime) [Lampe.Crypto.Bn254.Prime p]
    (domain : List (BitVec 8)) {n : Nat}
    (inputs : List.Vector (Fp p) n) (separator : Nat) : Point p :=
  encodeCurvePoint
    (∑ i : Fin n,
      Scalar.valueNat (Scalar.canonicalDecomp (inputs.get i)) •
        pedersenGenerator (p := p) domain (separator + i.val))

/-- Unfolding lemma for `pedersenCommitment`, in the shape produced by
the stdlib `_spec_canonical` proofs. -/
theorem pedersenCommitment_eq (p : Prime) [Lampe.Crypto.Bn254.Prime p]
    (domain : List (BitVec 8)) {n : Nat}
    (inputs : List.Vector (Fp p) n) (separator : Nat) :
    pedersenCommitment p domain inputs separator =
      encodeCurvePoint
        (∑ i : Fin n,
          Scalar.valueNat (Scalar.canonicalDecomp (inputs.get i)) •
            pedersenGenerator (p := p) domain (separator + i.val)) := rfl

/-- Pure Pedersen hash: the x-coordinate of the Pedersen commitment
MSM extended with the length-slot term
`n • pedersenGenerator pedersenHashLengthBytes 0` (the length-slot
domain is fixed by Barretenberg regardless of `domain`). This is the
exact closed form that the stdlib `pedersen_hash*_spec_canonical`
theorems guarantee for Noir's `std::hash::pedersen_hash_with_separator`. -/
def pedersenHash (p : Prime) [Lampe.Crypto.Bn254.Prime p]
    (domain : List (BitVec 8)) {n : Nat}
    (inputs : List.Vector (Fp p) n) (separator : Nat) : Fp p :=
  pointX
    (encodeCurvePoint
      ((∑ i : Fin n,
          Scalar.valueNat (Scalar.canonicalDecomp (inputs.get i)) •
            pedersenGenerator (p := p) domain (separator + i.val))
        + n • pedersenGenerator (p := p) pedersenHashLengthBytes 0))

/-- Unfolding lemma for `pedersenHash`, in the shape produced by the
stdlib `_spec_canonical` proofs. -/
theorem pedersenHash_eq (p : Prime) [Lampe.Crypto.Bn254.Prime p]
    (domain : List (BitVec 8)) {n : Nat}
    (inputs : List.Vector (Fp p) n) (separator : Nat) :
    pedersenHash p domain inputs separator =
      pointX
        (encodeCurvePoint
          ((∑ i : Fin n,
              Scalar.valueNat (Scalar.canonicalDecomp (inputs.get i)) •
                pedersenGenerator (p := p) domain (separator + i.val))
            + n • pedersenGenerator (p := p) pedersenHashLengthBytes 0)) := rfl

end Lampe.Crypto.Pedersen
