import Lampe.Crypto.WordUtils
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

Validation: see `Lampe/Tests/Blake3.lean`. Inputs follow the canonical
BLAKE3 test-vector convention `input[i] = i % 251`, and outputs are
taken from the official BLAKE3 Python binding (`pip install blake3`),
which is maintained by the BLAKE3 team and known to match the
published `test_vectors.json`.

Regenerate test vectors with `scripts/blake3_ref.py`.
-/

namespace Lampe.Crypto.Blake3

/-! ### Constants -/

/-- BLAKE3 IV — exactly SHA-256's initial hash value, shared as
`Lampe.Crypto.sha256IV`. -/
def iv : Array (BitVec 32) := sha256IV

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

/-! ### Chunk and parent processing

Byte ↔ word conversion (`bytesToWord`, `blockBytesToWords`,
`wordToBytes`, `stateTo32Bytes`, `padBlock`) is shared with BLAKE2s
via `Lampe.Crypto.WordUtils`. -/

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
  let numChunks := if bytes.size = 0 then 1 else (bytes.size + CHUNK_LEN - 1) / CHUNK_LEN
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

end Lampe.Crypto.Blake3
