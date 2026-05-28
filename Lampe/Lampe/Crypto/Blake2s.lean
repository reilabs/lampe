import Lampe.Tp

/-!
# BLAKE2s — concrete reference semantics

A computable Lean 4 implementation of BLAKE2s (the 32-bit, 32-byte
digest variant of BLAKE2) matching RFC 7693. We support the unkeyed
mode only, which is what Noir's `__blake2s` foreign builtin exposes.

References:
- RFC 7693 (sections 2-3 and Appendix A.2):
  https://datatracker.ietf.org/doc/html/rfc7693
- Reference C implementation:
  https://github.com/BLAKE2/BLAKE2/tree/master/ref

Validation: see test vectors at the bottom. The canonical RFC 7693
vectors (`"abc"` etc.) are anchored against Python's
`hashlib.blake2s`, which wraps the BLAKE2 reference implementation
(`libb2`).

Regenerate test vectors with `scripts/blake2s_ref.py`.
-/

namespace Lampe.Crypto.Blake2s

/-! ### Constants -/

/-- BLAKE2s IV — same as SHA-256's initial hash values (RFC 7693
section 2.6). -/
def iv : Array (BitVec 32) :=
  #[0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
    0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32]

/-- BLAKE2 σ permutation table (RFC 7693 section 2.7). Ten
permutations of `0..15` selecting which message word feeds each G
call. BLAKE2s uses only the first ten rows (BLAKE2b uses twelve, with
rows 10/11 repeating rows 0/1). -/
def sigma : Array (Array Nat) :=
  #[#[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
    #[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
    #[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
    #[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
    #[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
    #[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
    #[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
    #[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
    #[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
    #[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

/-- BLAKE2s block size in bytes. -/
def BLOCK_LEN : Nat := 64

/-- BLAKE2s output length in bytes (the only one Noir exposes). -/
def OUT_LEN : Nat := 32

/-! ### G mixing function and rounds -/

/-- 32-bit rotate-right. -/
@[inline] def rotr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- BLAKE2s G mixing function (RFC 7693 section 3.1). Updates four
lanes `a, b, c, d` of the 16-word working state `v` using two message
words `x, y`. Rotation amounts for BLAKE2s are 16/12/8/7. -/
def gFn (v : Array (BitVec 32)) (a b c d : Nat) (x y : BitVec 32) :
    Array (BitVec 32) := Id.run do
  let mut s := v
  let va := s[a]! + s[b]! + x
  s := s.set! a va
  let vd := rotr32 (s[d]! ^^^ va) 16
  s := s.set! d vd
  let vc := s[c]! + vd
  s := s.set! c vc
  let vb := rotr32 (s[b]! ^^^ vc) 12
  s := s.set! b vb
  let va' := va + vb + y
  s := s.set! a va'
  let vd' := rotr32 (vd ^^^ va') 8
  s := s.set! d vd'
  let vc' := vc + vd'
  s := s.set! c vc'
  let vb' := rotr32 (vb ^^^ vc') 7
  s := s.set! b vb'
  return s

/-- One full BLAKE2s round (RFC 7693 section 3.2): four column G calls
followed by four diagonal G calls, using the round-indexed σ
permutation to pick message words. -/
def round (v : Array (BitVec 32)) (m : Array (BitVec 32)) (r : Nat) :
    Array (BitVec 32) := Id.run do
  let s := sigma[r]!
  let mut w := v
  -- Column step
  w := gFn w 0 4  8 12 m[s[ 0]!]! m[s[ 1]!]!
  w := gFn w 1 5  9 13 m[s[ 2]!]! m[s[ 3]!]!
  w := gFn w 2 6 10 14 m[s[ 4]!]! m[s[ 5]!]!
  w := gFn w 3 7 11 15 m[s[ 6]!]! m[s[ 7]!]!
  -- Diagonal step
  w := gFn w 0 5 10 15 m[s[ 8]!]! m[s[ 9]!]!
  w := gFn w 1 6 11 12 m[s[10]!]! m[s[11]!]!
  w := gFn w 2 7  8 13 m[s[12]!]! m[s[13]!]!
  w := gFn w 3 4  9 14 m[s[14]!]! m[s[15]!]!
  return w

/-- BLAKE2s compression function `F(h, m, t, f)` (RFC 7693 section
3.2). Takes the 8-word chaining state `h`, a 16-word message block
`m`, the 64-bit counter `t`, and the final-block flag `f`. Returns
the updated 8-word chaining state. -/
def compress (h : Array (BitVec 32)) (m : Array (BitVec 32))
    (t : BitVec 64) (isFinal : Bool) : Array (BitVec 32) := Id.run do
  let tLo : BitVec 32 := t.truncate 32
  let tHi : BitVec 32 := (t >>> (32 : Nat)).truncate 32
  let f0 : BitVec 32 := if isFinal then 0xffffffff#32 else 0#32
  let f1 : BitVec 32 := 0#32
  -- Initialise working state v[0..15] = h[0..7] ‖ IV ⊕ (·, ·, t0, t1, f0, f1)
  let mut v : Array (BitVec 32) := Array.replicate 16 0
  for i in [:8] do v := v.set! i h[i]!
  for i in [:4] do v := v.set! (8 + i) iv[i]!
  v := v.set! 12 (iv[4]! ^^^ tLo)
  v := v.set! 13 (iv[5]! ^^^ tHi)
  v := v.set! 14 (iv[6]! ^^^ f0)
  v := v.set! 15 (iv[7]! ^^^ f1)
  -- 10 rounds (BLAKE2s).
  for r in [:10] do
    v := round v m r
  -- XOR halves back into the chaining state.
  let mut hOut := h
  for i in [:8] do
    hOut := hOut.set! i (h[i]! ^^^ v[i]! ^^^ v[i + 8]!)
  return hOut

/-! ### Byte ↔ word conversion (little-endian) -/

/-- Pack 4 little-endian bytes into a u32. -/
def bytesToWord (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  b0.zeroExtend 32 ||| (b1.zeroExtend 32 <<< (8 : Nat))
    ||| (b2.zeroExtend 32 <<< (16 : Nat))
    ||| (b3.zeroExtend 32 <<< (24 : Nat))

/-- Pack 64 bytes (one BLAKE2s block) into 16 u32 little-endian words.
The caller is responsible for zero-padding short final blocks. -/
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

/-- Serialise the 8-word chaining state as 32 little-endian bytes
(BLAKE2s-256 digest). -/
def stateTo32Bytes (h : Array (BitVec 32)) : Array (BitVec 8) := Id.run do
  let mut out : Array (BitVec 8) := Array.replicate 32 0
  for i in [:8] do
    let bs := wordToBytes h[i]!
    out := out.set! (4*i) bs[0]!
    out := out.set! (4*i + 1) bs[1]!
    out := out.set! (4*i + 2) bs[2]!
    out := out.set! (4*i + 3) bs[3]!
  return out

/-! ### Top-level entry points -/

/-- Initial chaining state for unkeyed BLAKE2s-256. RFC 7693 section
2.5: `h[0] := IV[0] XOR (0x0101kknn)` where `kk = 0` (no key) and
`nn = OUT_LEN = 32`, so the XOR mask is `0x01010020`. The other
parameter-block bytes (fanout = 1, depth = 1) are already part of
that low-byte mask via `0x01_01_00_20` (depth/fanout in the next two
bytes, both `0x01`). -/
def initialState : Array (BitVec 32) := Id.run do
  let mut h := iv
  h := h.set! 0 (h[0]! ^^^ 0x01010020#32)
  return h

/-- Pad a block of fewer than 64 bytes up to 64 bytes with trailing
zeros. -/
def padBlock (block : Array (BitVec 8)) : Array (BitVec 8) :=
  if block.size ≥ BLOCK_LEN then block.extract 0 BLOCK_LEN
  else block ++ Array.replicate (BLOCK_LEN - block.size) 0

/-- Sequential BLAKE2s compression over an arbitrary-length byte
input. Implements the loop from RFC 7693 section 3.3:

- All non-final blocks are compressed with `(t = byteCount, f = 0)`.
- The final block is zero-padded and compressed with
  `(t = totalLen, f = true)`.
- For empty input, a single zero-padded final block is compressed with
  `(t = 0, f = true)`.
-/
def blake2sHashBytes (input : Array (BitVec 8)) : Array (BitVec 8) := Id.run do
  let inputLen := input.size
  let mut h := initialState
  if inputLen = 0 then
    -- Empty input: one final compression with an all-zero block and t = 0.
    let block := padBlock #[]
    h := compress h (blockBytesToWords block) 0 true
  else
    let numBlocks := (inputLen + BLOCK_LEN - 1) / BLOCK_LEN
    for bi in [:numBlocks] do
      let blockStart := bi * BLOCK_LEN
      let blockEnd := Nat.min (blockStart + BLOCK_LEN) inputLen
      let isLast := bi + 1 = numBlocks
      let block := padBlock (input.extract blockStart blockEnd)
      let bytesSoFar : Nat :=
        if isLast then inputLen else blockStart + BLOCK_LEN
      let t : BitVec 64 := BitVec.ofNat 64 bytesSoFar
      h := compress h (blockBytesToWords block) t isLast
  return stateTo32Bytes h

/-- Concrete BLAKE2s hash. Matches the signature the foreign builtin
descriptor uses: input is a length-`N` array of bytes, output is the
fixed 32-byte digest. -/
def blake2sHash {p : Prime} {N : U 32}
    (input : Tp.denote p ((Tp.u 8).array N)) :
    Tp.denote p ((Tp.u 8).array (32 : U 32)) :=
  let outBytes := blake2sHashBytes input.toList.toArray
  List.Vector.ofFn (fun (i : Fin 32) => outBytes.getD i.val 0)

/-! ### Test vectors

The first two vectors (`empty`, `abc`) are the canonical RFC 7693
references; the latter two cover the block-boundary edge cases.
Outputs are computed by Python's `hashlib.blake2s`, which wraps the
BLAKE2 reference implementation (`libb2`). Regenerate with
`scripts/blake2s_ref.py`. -/

-- empty: RFC 7693 reference empty-input hash, input length = 0
private def emptyIn : Array (BitVec 8) :=
  #[]
private def emptyOut : Array (BitVec 8) :=
  #[0x69#8, 0x21#8, 0x7a#8, 0x30#8, 0x79#8, 0x90#8, 0x80#8, 0x94#8,
    0xe1#8, 0x11#8, 0x21#8, 0xd0#8, 0x42#8, 0x35#8, 0x4a#8, 0x7c#8,
    0x1f#8, 0x55#8, 0xb6#8, 0x48#8, 0x2c#8, 0xa1#8, 0xa5#8, 0x1e#8,
    0x1b#8, 0x25#8, 0x0d#8, 0xfd#8, 0x1e#8, 0xd0#8, 0xee#8, 0xf9#8]
theorem blake2s_empty_correct :
    blake2sHashBytes emptyIn = emptyOut := by native_decide

-- abc: RFC 7693 reference 'abc' hash, input length = 3
private def abcIn : Array (BitVec 8) :=
  #[0x61#8, 0x62#8, 0x63#8]
private def abcOut : Array (BitVec 8) :=
  #[0x50#8, 0x8c#8, 0x5e#8, 0x8c#8, 0x32#8, 0x7c#8, 0x14#8, 0xe2#8,
    0xe1#8, 0xa7#8, 0x2b#8, 0xa3#8, 0x4e#8, 0xeb#8, 0x45#8, 0x2f#8,
    0x37#8, 0x45#8, 0x8b#8, 0x20#8, 0x9e#8, 0xd6#8, 0x3a#8, 0x29#8,
    0x4d#8, 0x99#8, 0x9b#8, 0x4c#8, 0x86#8, 0x67#8, 0x59#8, 0x82#8]
theorem blake2s_abc_correct :
    blake2sHashBytes abcIn = abcOut := by native_decide

-- oneBlock: exactly one full BLAKE2s message block, input length = 64
private def oneBlockIn : Array (BitVec 8) :=
  ((List.range 64).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def oneBlockOut : Array (BitVec 8) :=
  #[0x56#8, 0xf3#8, 0x4e#8, 0x8b#8, 0x96#8, 0x55#8, 0x7e#8, 0x90#8,
    0xc1#8, 0xf2#8, 0x4b#8, 0x52#8, 0xd0#8, 0xc8#8, 0x9d#8, 0x51#8,
    0x08#8, 0x6a#8, 0xcf#8, 0x1b#8, 0x00#8, 0xf6#8, 0x34#8, 0xcf#8,
    0x1d#8, 0xde#8, 0x92#8, 0x33#8, 0xb8#8, 0xea#8, 0xaa#8, 0x3e#8]
theorem blake2s_oneBlock_correct :
    blake2sHashBytes oneBlockIn = oneBlockOut := by native_decide

-- overBlock: one byte past block boundary (two compressions), input length = 65
private def overBlockIn : Array (BitVec 8) :=
  ((List.range 65).map (fun i => BitVec.ofNat 8 (i % 251))).toArray
private def overBlockOut : Array (BitVec 8) :=
  #[0x1b#8, 0x53#8, 0xee#8, 0x94#8, 0xaa#8, 0xf3#8, 0x4e#8, 0x4b#8,
    0x15#8, 0x9d#8, 0x48#8, 0xde#8, 0x35#8, 0x2c#8, 0x7f#8, 0x06#8,
    0x61#8, 0xd0#8, 0xa4#8, 0x0e#8, 0xdf#8, 0xf9#8, 0x5a#8, 0x0b#8,
    0x16#8, 0x39#8, 0xb4#8, 0x09#8, 0x0e#8, 0x97#8, 0x44#8, 0x72#8]
theorem blake2s_overBlock_correct :
    blake2sHashBytes overBlockIn = overBlockOut := by native_decide

end Lampe.Crypto.Blake2s
