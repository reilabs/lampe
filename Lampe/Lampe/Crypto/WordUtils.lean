/-!
# Shared 32-bit word utilities for the hash-function family

Helpers shared by the concrete SHA-256, BLAKE2s and BLAKE3 reference
models (`Lampe/Crypto/Sha256.lean`, `Blake2s.lean`, `Blake3.lean`):

- 32-bit rotation (`rotr32`);
- little-endian byte ↔ `u32` word packing for the 64-byte block shape
  all three functions share (`bytesToWord`, `blockBytesToWords`,
  `wordToBytes`, `stateTo32Bytes`, `padBlock`);
- the SHA-256 initial hash value (`sha256IV`), which BLAKE2s and
  BLAKE3 reuse verbatim as their IV.

Note that SHA-256 itself is big-endian at the byte level; it only uses
`rotr32` and `sha256IV` from here. The little-endian byte conversions
are shared between the two BLAKE variants.
-/

namespace Lampe.Crypto

/-- 32-bit rotate-right. -/
@[inline] def rotr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- FIPS 180-4 §5.3.3: the SHA-256 initial hash value `H(0)` — the
first 32 bits of the fractional parts of the square roots of the first
8 primes.

This is exactly the constant BLAKE2s (RFC 7693 §2.6) and BLAKE3
(spec §2.1) use as their IV, so all three hash models share it. -/
def sha256IV : Array (BitVec 32) :=
  #[0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
    0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32]

/-- Pack 4 little-endian bytes into a u32. -/
def bytesToWord (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< (8 : Nat))
    ||| (b2.zeroExtend 32 <<< (16 : Nat))
    ||| (b3.zeroExtend 32 <<< (24 : Nat))

/-- Pack 64 bytes (one BLAKE2s/BLAKE3 block) into 16 u32 little-endian
words. The caller is responsible for zero-padding short final blocks
(see `padBlock`). -/
def blockBytesToWords (block : Array (BitVec 8)) : Array (BitVec 32) := Id.run do
  let mut out : Array (BitVec 32) := Array.replicate 16 0
  for i in [:16] do
    let b0 := block[4*i]!
    let b1 := block[4*i + 1]!
    let b2 := block[4*i + 2]!
    let b3 := block[4*i + 3]!
    out := out.set! i (bytesToWord b0 b1 b2 b3)
  return out

/-- Unpack a u32 to 4 little-endian bytes. -/
def wordToBytes (w : BitVec 32) : Array (BitVec 8) :=
  #[ w.truncate 8,
     (w >>> ( 8 : Nat)).truncate 8,
     (w >>> (16 : Nat)).truncate 8,
     (w >>> (24 : Nat)).truncate 8 ]

/-- Serialise the first 8 words of a state as 32 little-endian bytes
(the 32-byte digest shape of BLAKE2s and BLAKE3). -/
def stateTo32Bytes (s : Array (BitVec 32)) : Array (BitVec 8) := Id.run do
  let mut out : Array (BitVec 8) := Array.replicate 32 0
  for i in [:8] do
    let bs := wordToBytes s[i]!
    out := out.set! (4*i) bs[0]!
    out := out.set! (4*i + 1) bs[1]!
    out := out.set! (4*i + 2) bs[2]!
    out := out.set! (4*i + 3) bs[3]!
  return out

/-- `stateTo32Bytes` always produces exactly 32 bytes. -/
theorem size_stateTo32Bytes (s : Array (BitVec 32)) :
    (stateTo32Bytes s).size = 32 := by
  simp [stateTo32Bytes, List.range']

/-- Pad a block of fewer than 64 bytes up to the 64-byte block size
shared by BLAKE2s and BLAKE3 with trailing zeros (longer inputs are
truncated to one block). -/
def padBlock (block : Array (BitVec 8)) : Array (BitVec 8) :=
  if block.size ≥ 64 then block.extract 0 64
  else block ++ Array.replicate (64 - block.size) 0

end Lampe.Crypto
