import Lampe.Tp

/-!
# AES-128-CBC — concrete reference semantics (FIPS 197 + NIST SP 800-38A §6.2)

A computable Lean 4 implementation of AES-128 in CBC mode, matching
the Noir compiler builtin `aes128_encrypt`. The Noir contract is that
the builtin's input is a multiple of 16 bytes — the Noir stdlib
wrapper PKCS#7-pads to that shape before the foreign call. The Lean
function modelled here (`aes128Encrypt`) is defined for arbitrary
`N : U 32` so that the builtin descriptor is total; for `N` not a
multiple of 16 it adopts the convention of CBC over the truncated
prefix, zero-padded back to length `N`. The wrapper proof never
exercises that branch.

References:
- FIPS 197: Advanced Encryption Standard, §5.1 (cipher), §5.2 (key
  expansion), Appendix B (S-box), Appendix C (test vectors).
- NIST SP 800-38A §6.2: CBC mode.

The implementation is "direct": each transformation (`subBytes`,
`shiftRows`, `mixColumns`, `addRoundKey`) is defined inline against
the AES state. We avoid clever encodings — readability and the
ability for `native_decide` to evaluate on small inputs are the only
priorities.

State layout (FIPS 197 §3.4): the AES state is a 4×4 matrix of bytes
arranged column-major as `state[r + 4 * c]` for `r, c ∈ {0..3}`.
-/

namespace Lampe.Crypto.Aes128

/-! ### S-box (FIPS 197 Appendix B, Table 6) -/

set_option maxRecDepth 2048 in
/-- AES S-box: 256-byte substitution table. -/
def sbox : List.Vector (BitVec 8) 256 :=
  ⟨[
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
  ], by decide⟩

/-! ### Round constants (FIPS 197 §5.2, Rcon[i]) -/

/-- AES round constants for key expansion. `rcon[i]` is the leading byte
of `Rcon[i+1]` in FIPS 197 notation (the other three bytes are zero).
Only 10 entries are needed for AES-128 (rounds 1..10). -/
def rcon : List.Vector (BitVec 8) 10 :=
  ⟨[0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36], by decide⟩

/-! ### GF(2^8) multiplication -/

/-- Multiply a byte by `x` in `GF(2^8)` modulo the AES polynomial
`x^8 + x^4 + x^3 + x + 1` = `0x11b`. Equivalent to a left-shift
followed by conditional XOR with `0x1b`. -/
@[inline] def xtime (b : BitVec 8) : BitVec 8 :=
  let shifted := b <<< 1
  if b &&& 0x80#8 == 0 then shifted else shifted ^^^ 0x1b#8

/-- `GF(2^8)` multiplication by 2 (alias for `xtime`). -/
@[inline] def mul2 (b : BitVec 8) : BitVec 8 := xtime b

/-- `GF(2^8)` multiplication by 3 = `mul2 b ^^^ b`. -/
@[inline] def mul3 (b : BitVec 8) : BitVec 8 := xtime b ^^^ b

/-! ### State helpers

The AES state is a `List.Vector (BitVec 8) 16` arranged column-major:
byte `state[r + 4 * c]` is at row `r`, column `c`. -/

abbrev Block := List.Vector (BitVec 8) 16
abbrev Word := List.Vector (BitVec 8) 4

/-- The zero word (used as a fallback in list-based key expansion). -/
def zeroWord : Word := ⟨[0, 0, 0, 0], by decide⟩

/-- Look up an entry in the S-box; the index is the byte value. -/
@[inline] def sboxLookup (b : BitVec 8) : BitVec 8 :=
  sbox.get ⟨b.toNat, by have := b.isLt; simp; omega⟩

/-! ### Key expansion (FIPS 197 §5.2)

For AES-128 we generate 11 round keys (44 words = 176 bytes), starting
from the 16-byte cipher key. -/

/-- Apply S-box to each byte of a word. -/
@[inline] def subWord (w : Word) : Word :=
  List.Vector.ofFn (fun i => sboxLookup (w.get i))

/-- Rotate a word left by one byte: `[a, b, c, d] → [b, c, d, a]`. -/
@[inline] def rotWord (w : Word) : Word :=
  ⟨[w.get 1, w.get 2, w.get 3, w.get 0], rfl⟩

/-- XOR two words byte-wise. -/
@[inline] def xorWord (a b : Word) : Word :=
  List.Vector.ofFn (fun i => a.get i ^^^ b.get i)

/-- Read word `i` (4 bytes) from a flat byte vector. -/
@[inline] def readWord (key : Block) (i : Fin 4) : Word :=
  ⟨[ key.get ⟨4 * i.val,     by have := i.isLt; omega⟩,
     key.get ⟨4 * i.val + 1, by have := i.isLt; omega⟩,
     key.get ⟨4 * i.val + 2, by have := i.isLt; omega⟩,
     key.get ⟨4 * i.val + 3, by have := i.isLt; omega⟩ ], rfl⟩

/-- Compute the next word in the key schedule given the previous word
and the word four positions back. `i` is the index of the new word
(must be ≥ 4). -/
def nextScheduleWord (i : Nat) (prev wMinus4 : Word) : Word :=
  let t :=
    if i % 4 == 0 then
      let sub := subWord (rotWord prev)
      let r := rcon.get ⟨(i / 4 - 1) % 10, Nat.mod_lt _ (by decide)⟩
      (⟨[sub.get 0 ^^^ r, sub.get 1, sub.get 2, sub.get 3], rfl⟩ : Word)
    else
      prev
  xorWord wMinus4 t

/-- Append one new word to an in-progress key schedule list. -/
def stepKeySchedule (ws : List Word) : List Word :=
  let i := ws.length
  let prev := ws.getD (i - 1) zeroWord
  let wMinus4 := ws.getD (i - 4) zeroWord
  ws ++ [nextScheduleWord i prev wMinus4]

/-- Apply `stepKeySchedule` `n` times. -/
def iterateKeySchedule : Nat → List Word → List Word
  | 0, ws => ws
  | n + 1, ws => iterateKeySchedule n (stepKeySchedule ws)

/-- Build the schedule of 44 words for AES-128 key expansion. -/
def expandKeyWords (key : Block) : List Word :=
  let initial : List Word :=
    [readWord key 0, readWord key 1, readWord key 2, readWord key 3]
  iterateKeySchedule 40 initial

/-- Compose a 16-byte block from 4 consecutive words in a list. -/
def packRoundKey (ws : List Word) (k : Nat) : Block :=
  let w0 := ws.getD (4 * k) zeroWord
  let w1 := ws.getD (4 * k + 1) zeroWord
  let w2 := ws.getD (4 * k + 2) zeroWord
  let w3 := ws.getD (4 * k + 3) zeroWord
  ⟨[ w0.get 0, w0.get 1, w0.get 2, w0.get 3,
     w1.get 0, w1.get 1, w1.get 2, w1.get 3,
     w2.get 0, w2.get 1, w2.get 2, w2.get 3,
     w3.get 0, w3.get 1, w3.get 2, w3.get 3 ], rfl⟩

/-- The 11 round keys for AES-128, each 16 bytes. -/
def keyExpansion (key : Block) : List.Vector Block 11 :=
  let ws := expandKeyWords key
  List.Vector.ofFn (fun (k : Fin 11) => packRoundKey ws k.val)

/-! ### Round transformations (FIPS 197 §5.1) -/

/-- SubBytes: apply S-box to each byte. -/
def subBytes (s : Block) : Block :=
  List.Vector.ofFn (fun i => sboxLookup (s.get i))

/-- ShiftRows: row `r` shifts left by `r` positions (FIPS 197 §5.1.2).
With column-major layout `state[r + 4c]`, row `r` consists of bytes
at indices `r, r+4, r+8, r+12`; shifting left by `r` columns sources
the byte at `(r, c)` from `(r, c + r mod 4)`. -/
def shiftRows (s : Block) : Block :=
  List.Vector.ofFn (fun (i : Fin 16) =>
    let r : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
    let c : Fin 4 := ⟨i.val / 4, by have := i.isLt; omega⟩
    let srcC : Nat := (c.val + r.val) % 4
    let srcIdx : Fin 16 := ⟨r.val + 4 * srcC, by
      have hr := r.isLt
      have : srcC < 4 := Nat.mod_lt _ (by decide)
      omega⟩
    s.get srcIdx)

/-- MixColumns on a single column (FIPS 197 §5.1.3). -/
@[inline] def mixColumn (s0 s1 s2 s3 : BitVec 8) : Word :=
  ⟨[ mul2 s0 ^^^ mul3 s1 ^^^ s2       ^^^ s3,
     s0       ^^^ mul2 s1 ^^^ mul3 s2 ^^^ s3,
     s0       ^^^ s1       ^^^ mul2 s2 ^^^ mul3 s3,
     mul3 s0 ^^^ s1       ^^^ s2       ^^^ mul2 s3 ], rfl⟩

/-- MixColumns: apply `mixColumn` to each of the 4 columns. -/
def mixColumns (s : Block) : Block :=
  let col (c : Fin 4) : Word := mixColumn
    (s.get ⟨4 * c.val,     by have := c.isLt; omega⟩)
    (s.get ⟨4 * c.val + 1, by have := c.isLt; omega⟩)
    (s.get ⟨4 * c.val + 2, by have := c.isLt; omega⟩)
    (s.get ⟨4 * c.val + 3, by have := c.isLt; omega⟩)
  let c0 := col 0
  let c1 := col 1
  let c2 := col 2
  let c3 := col 3
  ⟨[ c0.get 0, c0.get 1, c0.get 2, c0.get 3,
     c1.get 0, c1.get 1, c1.get 2, c1.get 3,
     c2.get 0, c2.get 1, c2.get 2, c2.get 3,
     c3.get 0, c3.get 1, c3.get 2, c3.get 3 ], rfl⟩

/-- AddRoundKey: XOR the round key into the state. -/
def addRoundKey (s rk : Block) : Block :=
  List.Vector.ofFn (fun i => s.get i ^^^ rk.get i)

/-- One full round (rounds 1..9): SubBytes → ShiftRows → MixColumns → AddRoundKey. -/
def aesRound (s rk : Block) : Block :=
  addRoundKey (mixColumns (shiftRows (subBytes s))) rk

/-- Final round (round 10): no MixColumns. -/
def aesFinalRound (s rk : Block) : Block :=
  addRoundKey (shiftRows (subBytes s)) rk

/-- Encrypt a single 16-byte block with AES-128 (ECB). -/
def aesBlockEncrypt (key : Block) (input : Block) : Block :=
  let rks := keyExpansion key
  let s0 := addRoundKey input (rks.get 0)
  -- Rounds 1..9
  let s9 := (List.finRange 9).foldl
    (fun s (i : Fin 9) => aesRound s (rks.get ⟨i.val + 1, by have := i.isLt; omega⟩))
    s0
  -- Final round (round 10)
  aesFinalRound s9 (rks.get 10)

/-! ### CBC mode (NIST SP 800-38A §6.2) -/

/-- XOR two 16-byte blocks. -/
@[inline] def xorBlock (a b : Block) : Block :=
  List.Vector.ofFn (fun i => a.get i ^^^ b.get i)

/-- CBC chain over a list of blocks. `prev` is the previous ciphertext
block (or the IV for the first block). -/
def aesCbcEncryptBlocks (key : Block) :
    (prev : Block) → (blocks : List Block) → List Block
  | _, [] => []
  | prev, b :: rest =>
    let cipher := aesBlockEncrypt key (xorBlock b prev)
    cipher :: aesCbcEncryptBlocks key cipher rest

theorem aesCbcEncryptBlocks_length (key : Block) :
    ∀ (prev : Block) (blocks : List Block),
      (aesCbcEncryptBlocks key prev blocks).length = blocks.length
  | _, [] => rfl
  | prev, b :: rest => by
    simp [aesCbcEncryptBlocks, aesCbcEncryptBlocks_length key _ rest]

/-! ### Byte ↔ Block conversion -/

/-- Take exactly 16 bytes from a list, padding with zero if short. -/
def takeBlock16 (bs : List (BitVec 8)) : Block :=
  ⟨[ bs.getD 0 0, bs.getD 1 0, bs.getD 2 0, bs.getD 3 0,
     bs.getD 4 0, bs.getD 5 0, bs.getD 6 0, bs.getD 7 0,
     bs.getD 8 0, bs.getD 9 0, bs.getD 10 0, bs.getD 11 0,
     bs.getD 12 0, bs.getD 13 0, bs.getD 14 0, bs.getD 15 0 ], rfl⟩

/-- Build a `Block` from 16 explicit bytes. -/
@[inline] def mkBlock
    (b0 b1 b2 b3 b4 b5 b6 b7
     b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : Block :=
  ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], rfl⟩

/-- Split a flat byte list of length `16 * k` into `k` 16-byte blocks.
The `k` argument supplies the expected block count up front, avoiding
the partial-match awkwardness of a length-driven recursion. -/
def splitBlocks : (k : Nat) → List (BitVec 8) → List Block
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
    b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: rest =>
    mkBlock b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 ::
    splitBlocks k rest
  | _ + 1, _ => []  -- list shorter than 16 with k ≥ 1: degenerate

theorem splitBlocks_length_of_eq :
    ∀ (k : Nat) (l : List (BitVec 8)), l.length = 16 * k →
      (splitBlocks k l).length = k := by
  intro k l h
  induction k generalizing l with
  | zero => simp [splitBlocks]
  | succ k ih =>
    match l, h with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
      b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: rest, h =>
      simp only [splitBlocks, List.length_cons]
      have hrest : rest.length = 16 * k := by
        simp [List.length_cons] at h
        omega
      have := ih rest hrest
      omega
    | [], h => simp at h
    | [_], h => simp [List.length_cons] at h; omega
    | [_, _], h => simp [List.length_cons] at h; omega
    | [_, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _], h => simp [List.length_cons] at h; omega

/-- Concatenate a list of 16-byte blocks into a flat byte list. -/
def flattenBlocks (blocks : List Block) : List (BitVec 8) :=
  blocks.flatMap (·.toList)

theorem flattenBlocks_length (blocks : List Block) :
    (flattenBlocks blocks).length = 16 * blocks.length := by
  induction blocks with
  | nil => rfl
  | cons b rest ih =>
    simp only [flattenBlocks, List.flatMap_cons, List.length_append, List.length_cons]
    have hb : b.toList.length = 16 := b.toList_length
    simp only [flattenBlocks] at ih
    omega

/-! ### Top-level entry points -/

/-- AES-128-CBC encryption of an already-padded input (multiple of 16
bytes). This matches the semantics of the Noir foreign builtin
`aes128_encrypt`. -/
def aes128CbcEncryptRaw (key iv : Block) (input : List (BitVec 8)) : List (BitVec 8) :=
  flattenBlocks (aesCbcEncryptBlocks key iv (splitBlocks (input.length / 16) input))

/-- PKCS#7 padding (RFC 5652 §6.3): if the input length is `N`, append
`16 - N % 16` copies of the byte `(16 - N % 16) : u8` to reach a
multiple of 16. Note that when `N` is already a multiple of 16, a full
extra 16-byte block of `0x10` is appended. -/
def pkcs7Pad (input : List (BitVec 8)) : List (BitVec 8) :=
  let n := input.length
  let padLen := 16 - n % 16
  input ++ List.replicate padLen (BitVec.ofNat 8 padLen)

theorem pkcs7Pad_length (input : List (BitVec 8)) :
    (pkcs7Pad input).length = input.length + 16 - input.length % 16 := by
  simp [pkcs7Pad, List.length_append, List.length_replicate]
  have : input.length % 16 < 16 := Nat.mod_lt _ (by decide)
  omega

theorem pkcs7Pad_length_div16 (input : List (BitVec 8)) :
    (pkcs7Pad input).length % 16 = 0 := by
  simp [pkcs7Pad, List.length_append, List.length_replicate]
  have h : input.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have : input.length + (16 - input.length % 16) = 16 * (input.length / 16 + 1) := by
    have heq : input.length = 16 * (input.length / 16) + input.length % 16 :=
      (Nat.div_add_mod input.length 16).symm
    omega
  rw [this]
  exact Nat.mul_mod_right 16 _

/-- AES-128-CBC encryption with PKCS#7 padding. This is what the Noir
`std::aes128::aes128_encrypt` wrapper computes. -/
def aes128CbcEncryptPkcs7 {n : Nat}
    (key iv : Block) (input : List.Vector (BitVec 8) n) :
    List.Vector (BitVec 8) (n + 16 - n % 16) :=
  let outList := aes128CbcEncryptRaw key iv (pkcs7Pad input.toList)
  ⟨outList, by
    -- Plan: padded length = n + 16 - n%16, divisible by 16. Split
    -- into k = (n + 16 - n%16) / 16 blocks; CBC preserves block count;
    -- flatten gives 16 * k = n + 16 - n%16 bytes.
    have htl : input.toList.length = n := input.toList_length
    have hpad : (pkcs7Pad input.toList).length = n + 16 - n % 16 := by
      have := pkcs7Pad_length input.toList
      rw [htl] at this
      exact this
    have hpad_mod : (pkcs7Pad input.toList).length % 16 = 0 :=
      pkcs7Pad_length_div16 input.toList
    -- Express padded length as 16 * k.
    set padL := (pkcs7Pad input.toList).length with hpadL
    have hk : padL = 16 * (padL / 16) := by
      have := Nat.div_add_mod padL 16
      omega
    have hsplit_len :
        (splitBlocks (padL / 16) (pkcs7Pad input.toList)).length = padL / 16 := by
      apply splitBlocks_length_of_eq
      exact hk
    -- Goal: outList.length = n + 16 - n % 16
    show outList.length = _
    simp only [outList, aes128CbcEncryptRaw, flattenBlocks_length,
      aesCbcEncryptBlocks_length]
    rw [hsplit_len]
    rw [← hk]
    exact hpad⟩

/-! ### Builtin entry point (called from `Lampe.Builtin.aes128Encrypt`)

The Noir builtin signature is `[u8; N] × [u8; 16] × [u8; 16] → [u8; N]`
where `N` is constrained (at the wrapper level) to be a multiple of 16.
When the precondition holds, this matches `aes128CbcEncryptRaw` on the
input, IV and key.

The builtin descriptor must be total over arbitrary `N : U 32`. For
`N` not a multiple of 16, we adopt the convention of running CBC over
the truncated `⌊N/16⌋ * 16` prefix and padding the result back out to
length `N` with zeros. This branch is never reached by the wrapper
proof but keeps the function total. -/
def aes128Encrypt {p : Prime} {N : U 32}
    (input : Tp.denote p ((Tp.u 8).array N))
    (iv : Tp.denote p ((Tp.u 8).array (16 : U 32)))
    (key : Tp.denote p ((Tp.u 8).array (16 : U 32))) :
    Tp.denote p ((Tp.u 8).array N) :=
  let outList := aes128CbcEncryptRaw key iv input.toList
  let padded := outList ++ List.replicate N.toNat 0
  let truncated := padded.take N.toNat
  ⟨truncated, by
    have h₁ : (outList ++ List.replicate N.toNat 0).length ≥ N.toNat := by
      simp [List.length_append, List.length_replicate]
    simp [truncated, List.length_take]
    omega⟩

/-! ### Bridge: builtin on padded input ↔ PKCS#7-padded CBC -/

theorem aesCbcEncryptBlocks_length' (key prev : Block) (blocks : List Block) :
    (aesCbcEncryptBlocks key prev blocks).length = blocks.length :=
  aesCbcEncryptBlocks_length key prev blocks

/-- When the builtin input length is exactly a multiple of 16, the
truncate-and-zero-pad postprocessing in `aes128Encrypt` is a no-op, so
the function reduces to `aes128CbcEncryptRaw` on the input. -/
theorem aes128Encrypt_toList_of_dvd16
    {p : Prime} {N : U 32}
    (input : Tp.denote p ((Tp.u 8).array N))
    (iv : Tp.denote p ((Tp.u 8).array (16 : U 32)))
    (key : Tp.denote p ((Tp.u 8).array (16 : U 32)))
    (hdvd : N.toNat % 16 = 0) :
    (aes128Encrypt input iv key).toList =
      aes128CbcEncryptRaw key iv input.toList := by
  -- Length of the raw CBC output: 16 * (input.length / 16) = input.length.
  have htl : input.toList.length = N.toNat := input.toList_length
  have hk : input.toList.length = 16 * (input.toList.length / 16) := by
    have hmod : input.toList.length % 16 = 0 := by rw [htl]; exact hdvd
    have hdm := Nat.div_add_mod input.toList.length 16
    omega
  have hsplit_len :
      (splitBlocks (input.toList.length / 16) input.toList).length =
        input.toList.length / 16 :=
    splitBlocks_length_of_eq _ _ hk
  have hraw_len : (aes128CbcEncryptRaw key iv input.toList).length =
      input.toList.length := by
    simp only [aes128CbcEncryptRaw, flattenBlocks_length,
      aesCbcEncryptBlocks_length, hsplit_len]
    omega
  have hraw_eq : (aes128CbcEncryptRaw key iv input.toList).length = N.toNat := by
    rw [hraw_len]; exact htl
  -- Reduce the take/append.
  show ((aes128CbcEncryptRaw key iv input.toList ++
          List.replicate N.toNat 0).take N.toNat) =
      aes128CbcEncryptRaw key iv input.toList
  rw [List.take_append_of_le_length (by rw [hraw_eq])]
  exact List.take_of_length_le (Nat.le_of_eq hraw_eq)

end Lampe.Crypto.Aes128
