import Lampe.Tp

/-!
# BLAKE3 — concrete reference semantics

A computable Lean 4 implementation of BLAKE3 (plain hash mode),
matching the official BLAKE3 specification:

- https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf
- Reference implementation:
  https://github.com/BLAKE3-team/BLAKE3/blob/master/reference_impl/

This file implements the full algorithm including the Merkle-tree
combination for inputs larger than one chunk (1024 bytes). Keyed-hash
and derive-key modes are not implemented (Noir doesn't expose them).

Validation: see test vectors at the bottom. Inputs follow the
canonical BLAKE3 test-vector convention `input[i] = i % 251`, and
outputs are taken from the official BLAKE3 Python binding
(`pip install blake3`), which is maintained by the BLAKE3 team and
known to match the published `test_vectors.json`. **Since any correct
BLAKE3 implementation must produce these outputs, including
Barretenberg's `__blake3` foreign call, matching them transitively
certifies agreement with the production ZK backend** — a divergence
would either be a bug in this Lean implementation or, far less
likely, a bug in Barretenberg's BLAKE3 that would invalidate every
Noir program using `blake3`.

Regenerate test vectors with `scripts/blake3_ref.py`.
-/

namespace Lampe.Crypto.Blake3

/-! ### Constants -/

/-- BLAKE3 IV (same as SHA-256's initial hash values). -/
def iv : Array (BitVec 32) :=
  #[0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
    0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32]

/-- Message-word permutation applied between rounds. -/
def msgPermutation : Array Nat :=
  #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

-- Domain-separation flags (BLAKE3 spec Table 3).
def CHUNK_START_FLAG : BitVec 32 := 0x01#32
def CHUNK_END_FLAG   : BitVec 32 := 0x02#32
def PARENT_FLAG      : BitVec 32 := 0x04#32
def ROOT_FLAG        : BitVec 32 := 0x08#32

/-- Block size in bytes. -/
def BLOCK_LEN : Nat := 64

/-- Chunk size in bytes (16 blocks). -/
def CHUNK_LEN : Nat := 1024

/-! ### G mixing function and rounds -/

/-- 32-bit rotate-right. -/
@[inline] def rotr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- BLAKE3 G mixing function: update four state lanes a/b/c/d using two
message words mx/my (BLAKE3 spec §2.3). -/
def gFn (state : Array (BitVec 32)) (a b c d : Nat) (mx my : BitVec 32) :
    Array (BitVec 32) := Id.run do
  let mut s := state
  let va := s[a]! + s[b]! + mx
  s := s.set! a va
  let vd := rotr32 (s[d]! ^^^ va) 16
  s := s.set! d vd
  let vc := s[c]! + vd
  s := s.set! c vc
  let vb := rotr32 (s[b]! ^^^ vc) 12
  s := s.set! b vb
  let va' := va + vb + my
  s := s.set! a va'
  let vd' := rotr32 (vd ^^^ va') 8
  s := s.set! d vd'
  let vc' := vc + vd'
  s := s.set! c vc'
  let vb' := rotr32 (vb ^^^ vc') 7
  s := s.set! b vb'
  return s

/-- One full BLAKE3 round: 4 column G calls then 4 diagonal G calls. -/
def round (state : Array (BitVec 32)) (m : Array (BitVec 32)) : Array (BitVec 32) := Id.run do
  let mut s := state
  -- Column round
  s := gFn s 0 4  8 12 m[0]!  m[1]!
  s := gFn s 1 5  9 13 m[2]!  m[3]!
  s := gFn s 2 6 10 14 m[4]!  m[5]!
  s := gFn s 3 7 11 15 m[6]!  m[7]!
  -- Diagonal round
  s := gFn s 0 5 10 15 m[8]!  m[9]!
  s := gFn s 1 6 11 12 m[10]! m[11]!
  s := gFn s 2 7  8 13 m[12]! m[13]!
  s := gFn s 3 4  9 14 m[14]! m[15]!
  return s

/-- Permute message words between rounds. -/
def permuteMsg (m : Array (BitVec 32)) : Array (BitVec 32) := Id.run do
  let mut out : Array (BitVec 32) := Array.replicate 16 0
  for i in [:16] do
    out := out.set! i m[msgPermutation[i]!]!
  return out

/-- BLAKE3 compression: 7 rounds applied to a 16-word state initialised
from `cv`, IV[0..3], counter, blockLen, flags. Returns the full 16-word
post-mix state. Callers take the first 8 words as the chaining-value
output, or all 16 as the root output. -/
def compress (cv : Array (BitVec 32)) (blockWords : Array (BitVec 32))
    (counter : BitVec 64) (blockLen flags : BitVec 32) : Array (BitVec 32) := Id.run do
  -- Initialize state v[0..15].
  let counterLo : BitVec 32 := counter.truncate 32
  let counterHi : BitVec 32 := (counter >>> (32 : Nat)).truncate 32
  let mut s : Array (BitVec 32) := Array.replicate 16 0
  for i in [:8] do s := s.set! i cv[i]!
  for i in [:4] do s := s.set! (8 + i) iv[i]!
  s := s.set! 12 counterLo
  s := s.set! 13 counterHi
  s := s.set! 14 blockLen
  s := s.set! 15 flags
  -- 7 rounds, permuting message between rounds.
  let mut m := blockWords
  for r in [:6] do
    s := round s m
    m := permuteMsg m
    let _ := r  -- suppress unused warning
  s := round s m
  -- Output finalisation: v[i] ^= v[i+8] for i < 8; v[i+8] ^= cv[i] for i < 8.
  for i in [:8] do
    s := s.set! i (s[i]! ^^^ s[i+8]!)
    s := s.set! (i + 8) (s[i+8]! ^^^ cv[i]!)
  return s

/-! ### Byte ↔ word conversion (little-endian) -/

/-- Pack 4 little-endian bytes into a u32. -/
def bytesToWord (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< (8 : Nat))
    ||| (b2.zeroExtend 32 <<< (16 : Nat))
    ||| (b3.zeroExtend 32 <<< (24 : Nat))

/-- Pack 64 bytes into 16 u32 little-endian words. The input array is
expected to have at least `start + 64` valid bytes; positions past
`inputLen` (the logical length) are zero-padded by the caller. -/
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

/-- Serialize the first 8 words of a state as 32 little-endian bytes
(BLAKE3 default output length). -/
def stateTo32Bytes (s : Array (BitVec 32)) : Array (BitVec 8) := Id.run do
  let mut out : Array (BitVec 8) := Array.replicate 32 0
  for i in [:8] do
    let bs := wordToBytes s[i]!
    out := out.set! (4*i) bs[0]!
    out := out.set! (4*i + 1) bs[1]!
    out := out.set! (4*i + 2) bs[2]!
    out := out.set! (4*i + 3) bs[3]!
  return out

/-! ### Chunk and parent processing -/

/-- Pad an arbitrary-length byte slice to a multiple of 64 bytes with
zero bytes. Returns the padded array and the original length (as the
final block's `blockLen` field). -/
def padBlock (bytes : Array (BitVec 8)) : Array (BitVec 8) :=
  if bytes.size ≥ 64 then bytes.extract 0 64
  else bytes ++ Array.replicate (64 - bytes.size) 0

/-- Process one chunk of up to 1024 bytes through up to 16 block
compressions. Returns the chaining value (first 8 words) by default,
or the full 16-word root output when `isRoot = true`. -/
def processChunk (chunkBytes : Array (BitVec 8)) (chunkCounter : BitVec 64)
    (isRoot : Bool) : Array (BitVec 32) := Id.run do
  let chunkLen := chunkBytes.size
  -- Number of blocks the chunk contains (ceil(chunkLen / 64)).
  let numBlocks := if chunkLen = 0 then 1 else (chunkLen + 63) / 64
  let mut cv : Array (BitVec 32) := iv  -- start each chunk with the IV
  let mut lastFullOutput : Array (BitVec 32) := Array.replicate 16 0
  for bi in [:numBlocks] do
    let blockStart := bi * 64
    let blockEnd := Nat.min (blockStart + 64) chunkLen
    let bLen := blockEnd - blockStart
    let blockSlice : Array (BitVec 8) := padBlock (chunkBytes.extract blockStart blockEnd)
    let blockWords := blockBytesToWords blockSlice
    let isFirst := bi = 0
    let isLast := bi + 1 = numBlocks
    let mut flags : BitVec 32 := 0
    if isFirst then flags := flags ||| CHUNK_START_FLAG
    if isLast then flags := flags ||| CHUNK_END_FLAG
    if isLast ∧ isRoot then flags := flags ||| ROOT_FLAG
    let out := compress cv blockWords chunkCounter (BitVec.ofNat 32 bLen) flags
    lastFullOutput := out
    -- Next block's CV is the first 8 words of this compression's output.
    cv := out.extract 0 8
  return if isRoot then lastFullOutput else cv

/-- Parent node: combine two child chaining values. Returns the full
16-word state when `isRoot = true`, otherwise the 8-word chaining
value. -/
def parentCV (leftCV rightCV : Array (BitVec 32)) (isRoot : Bool) :
    Array (BitVec 32) := Id.run do
  let mut blockWords : Array (BitVec 32) := Array.replicate 16 0
  for i in [:8] do
    blockWords := blockWords.set! i leftCV[i]!
    blockWords := blockWords.set! (i + 8) rightCV[i]!
  let mut flags : BitVec 32 := PARENT_FLAG
  if isRoot then flags := flags ||| ROOT_FLAG
  let out := compress iv blockWords 0 (BitVec.ofNat 32 BLOCK_LEN) flags
  return if isRoot then out else out.extract 0 8

/-! ### Tree construction -/

/-- Largest power of 2 ≤ `n` and < `2^31`. -/
def largestPowOf2Le (n : Nat) : Nat := Id.run do
  if n ≤ 1 then return 1
  let mut p := 1
  while 2 * p ≤ n do
    p := 2 * p
  return p

/-- Recursively hash a slice `chunkBytes[startChunk * 1024 : endChunk * 1024]`
of an already-validated input. `isRoot` is true only for the outermost
call; internal recursive calls combine via `parentCV` with `isRoot = false`. -/
partial def hashSubtree (input : Array (BitVec 8))
    (startChunk endChunk : Nat) (isRoot : Bool) : Array (BitVec 32) :=
  let numChunks := endChunk - startChunk
  if numChunks ≤ 1 then
    -- Single-chunk subtree: hash the chunk bytes directly.
    let chunkStart := startChunk * CHUNK_LEN
    let chunkEnd := Nat.min ((startChunk + 1) * CHUNK_LEN) input.size
    let chunkBytes := input.extract chunkStart chunkEnd
    processChunk chunkBytes (BitVec.ofNat 64 startChunk) isRoot
  else
    -- Split: left subtree holds the largest power of 2 < numChunks.
    let leftSize := largestPowOf2Le (numChunks - 1)
    let leftSize := if leftSize * 2 ≥ numChunks then leftSize else leftSize
    let mid := startChunk + leftSize
    let left := hashSubtree input startChunk mid false
    let right := hashSubtree input mid endChunk false
    -- For parent: only the 8-word CV portion of children is used.
    let leftCV := left.extract 0 8
    let rightCV := right.extract 0 8
    parentCV leftCV rightCV isRoot

/-! ### Top-level entry points -/

/-- Compute BLAKE3 over a byte array, returning the 32-byte digest as
an `Array`. This is the algorithmic core; `blake3Hash` is the
`Tp.denote`-typed wrapper that matches the builtin descriptor. -/
def blake3HashBytes (bytes : Array (BitVec 8)) : Array (BitVec 8) :=
  let inputLen := bytes.size
  let numChunks := if inputLen = 0 then 1 else (inputLen + CHUNK_LEN - 1) / CHUNK_LEN
  let rootOutput := hashSubtree bytes 0 numChunks true
  stateTo32Bytes rootOutput

/-- Concrete BLAKE3 hash. -/
def blake3Hash {p : Prime} {N : U 32}
    (input : Tp.denote p ((Tp.u 8).array N)) :
    Tp.denote p ((Tp.u 8).array (32 : U 32)) :=
  let outBytes := blake3HashBytes input.toList.toArray
  -- Convert to List.Vector (BitVec 8) 32. Use getD to make conversion total;
  -- in practice outBytes always has size 32 by construction.
  List.Vector.ofFn (fun (i : Fin 32) => outBytes.getD i.val 0)

/-! ### Test vectors

The inputs follow the canonical BLAKE3 test-vector pattern
`input[i] = i % 251`. Outputs are taken from the official BLAKE3
Python binding (`pip install blake3`), maintained by the BLAKE3 team
and known to match the published `test_vectors.json`. Regenerate with
`scripts/blake3_ref.py`. -/

-- empty: input = [i % 251 for i in 0..0], len = 0
private def emptyIn : Array (BitVec 8) :=
  #[]
private def emptyOut : Array (BitVec 8) :=
  #[0xaf#8, 0x13#8, 0x49#8, 0xb9#8, 0xf5#8, 0xf9#8, 0xa1#8, 0xa6#8, 0xa0#8, 0x40#8, 0x4d#8, 0xea#8, 0x36#8, 0xdc#8, 0xc9#8, 0x49#8, 0x9b#8, 0xcb#8, 0x25#8, 0xc9#8, 0xad#8, 0xc1#8, 0x12#8, 0xb7#8, 0xcc#8, 0x9a#8, 0x93#8, 0xca#8, 0xe4#8, 0x1f#8, 0x32#8, 0x62#8]
theorem blake3_empty_correct :
    blake3HashBytes emptyIn = emptyOut := by native_decide

-- oneByte: input = [i % 251 for i in 0..1], len = 1
private def oneByteIn : Array (BitVec 8) :=
  ((List.range 1).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def oneByteOut : Array (BitVec 8) :=
  #[0x2d#8, 0x3a#8, 0xde#8, 0xdf#8, 0xf1#8, 0x1b#8, 0x61#8, 0xf1#8, 0x4c#8, 0x88#8, 0x6e#8, 0x35#8, 0xaf#8, 0xa0#8, 0x36#8, 0x73#8, 0x6d#8, 0xcd#8, 0x87#8, 0xa7#8, 0x4d#8, 0x27#8, 0xb5#8, 0xc1#8, 0x51#8, 0x02#8, 0x25#8, 0xd0#8, 0xf5#8, 0x92#8, 0xe2#8, 0x13#8]
theorem blake3_oneByte_correct :
    blake3HashBytes oneByteIn = oneByteOut := by native_decide

-- underBlock: input = [i % 251 for i in 0..63], len = 63
private def underBlockIn : Array (BitVec 8) :=
  ((List.range 63).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def underBlockOut : Array (BitVec 8) :=
  #[0xe9#8, 0xbc#8, 0x37#8, 0xa5#8, 0x94#8, 0xda#8, 0xad#8, 0x83#8, 0xbe#8, 0x94#8, 0x70#8, 0xdf#8, 0x7f#8, 0x7b#8, 0x37#8, 0x98#8, 0x29#8, 0x7c#8, 0x3d#8, 0x83#8, 0x4c#8, 0xe8#8, 0x0b#8, 0xa8#8, 0x5d#8, 0x6e#8, 0x20#8, 0x76#8, 0x27#8, 0xb7#8, 0xdb#8, 0x7b#8]
theorem blake3_underBlock_correct :
    blake3HashBytes underBlockIn = underBlockOut := by native_decide

-- oneBlock: input = [i % 251 for i in 0..64], len = 64
private def oneBlockIn : Array (BitVec 8) :=
  ((List.range 64).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def oneBlockOut : Array (BitVec 8) :=
  #[0x4e#8, 0xed#8, 0x71#8, 0x41#8, 0xea#8, 0x4a#8, 0x5c#8, 0xd4#8, 0xb7#8, 0x88#8, 0x60#8, 0x6b#8, 0xd2#8, 0x3f#8, 0x46#8, 0xe2#8, 0x12#8, 0xaf#8, 0x9c#8, 0xac#8, 0xeb#8, 0xac#8, 0xdc#8, 0x7d#8, 0x1f#8, 0x4c#8, 0x6d#8, 0xc7#8, 0xf2#8, 0x51#8, 0x1b#8, 0x98#8]
theorem blake3_oneBlock_correct :
    blake3HashBytes oneBlockIn = oneBlockOut := by native_decide

-- overBlock: input = [i % 251 for i in 0..65], len = 65
private def overBlockIn : Array (BitVec 8) :=
  ((List.range 65).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def overBlockOut : Array (BitVec 8) :=
  #[0xde#8, 0x1e#8, 0x5f#8, 0xa0#8, 0xbe#8, 0x70#8, 0xdf#8, 0x6d#8, 0x2b#8, 0xe8#8, 0xff#8, 0xfd#8, 0x0e#8, 0x99#8, 0xce#8, 0xaa#8, 0x8e#8, 0xb6#8, 0xe8#8, 0xc9#8, 0x3a#8, 0x63#8, 0xf2#8, 0xd8#8, 0xd1#8, 0xc3#8, 0x0e#8, 0xcb#8, 0x6b#8, 0x26#8, 0x3d#8, 0xee#8]
theorem blake3_overBlock_correct :
    blake3HashBytes overBlockIn = overBlockOut := by native_decide

-- underChunk: input = [i % 251 for i in 0..1023], len = 1023
private def underChunkIn : Array (BitVec 8) :=
  ((List.range 1023).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def underChunkOut : Array (BitVec 8) :=
  #[0x10#8, 0x10#8, 0x89#8, 0x70#8, 0xee#8, 0xda#8, 0x3e#8, 0xb9#8, 0x32#8, 0xba#8, 0xac#8, 0x14#8, 0x28#8, 0xc7#8, 0xa2#8, 0x16#8, 0x3b#8, 0x0e#8, 0x92#8, 0x4c#8, 0x9a#8, 0x9e#8, 0x25#8, 0xb3#8, 0x5b#8, 0xba#8, 0x72#8, 0xb2#8, 0x8f#8, 0x70#8, 0xbd#8, 0x11#8]
theorem blake3_underChunk_correct :
    blake3HashBytes underChunkIn = underChunkOut := by native_decide

-- oneChunk: input = [i % 251 for i in 0..1024], len = 1024
private def oneChunkIn : Array (BitVec 8) :=
  ((List.range 1024).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def oneChunkOut : Array (BitVec 8) :=
  #[0x42#8, 0x21#8, 0x47#8, 0x39#8, 0xf0#8, 0x95#8, 0xa4#8, 0x06#8, 0xf3#8, 0xfc#8, 0x83#8, 0xde#8, 0xb8#8, 0x89#8, 0x74#8, 0x4a#8, 0xc0#8, 0x0d#8, 0xf8#8, 0x31#8, 0xc1#8, 0x0d#8, 0xaa#8, 0x55#8, 0x18#8, 0x9b#8, 0x5d#8, 0x12#8, 0x1c#8, 0x85#8, 0x5a#8, 0xf7#8]
theorem blake3_oneChunk_correct :
    blake3HashBytes oneChunkIn = oneChunkOut := by native_decide

-- overChunk: input = [i % 251 for i in 0..1025], len = 1025
private def overChunkIn : Array (BitVec 8) :=
  ((List.range 1025).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def overChunkOut : Array (BitVec 8) :=
  #[0xd0#8, 0x02#8, 0x78#8, 0xae#8, 0x47#8, 0xeb#8, 0x27#8, 0xb3#8, 0x4f#8, 0xae#8, 0xcf#8, 0x67#8, 0xb4#8, 0xfe#8, 0x26#8, 0x3f#8, 0x82#8, 0xd5#8, 0x41#8, 0x29#8, 0x16#8, 0xc1#8, 0xff#8, 0xd9#8, 0x7c#8, 0x8c#8, 0xb7#8, 0xfb#8, 0x81#8, 0x4b#8, 0x84#8, 0x44#8]
theorem blake3_overChunk_correct :
    blake3HashBytes overChunkIn = overChunkOut := by native_decide

-- twoChunks: input = [i % 251 for i in 0..2048], len = 2048
private def twoChunksIn : Array (BitVec 8) :=
  ((List.range 2048).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def twoChunksOut : Array (BitVec 8) :=
  #[0xe7#8, 0x76#8, 0xb6#8, 0x02#8, 0x8c#8, 0x7c#8, 0xd2#8, 0x2a#8, 0x4d#8, 0x0b#8, 0xa1#8, 0x82#8, 0xa8#8, 0xbf#8, 0x62#8, 0x20#8, 0x5d#8, 0x2e#8, 0xf5#8, 0x76#8, 0x46#8, 0x7e#8, 0x83#8, 0x8e#8, 0xd6#8, 0xf2#8, 0x52#8, 0x9b#8, 0x85#8, 0xfb#8, 0xa2#8, 0x4a#8]
theorem blake3_twoChunks_correct :
    blake3HashBytes twoChunksIn = twoChunksOut := by native_decide


end Lampe.Crypto.Blake3
