import Lampe.Crypto.WordUtils
import Lampe.Tp

/-!
# SHA-256 compression — concrete reference semantics

A computable Lean 4 implementation of one round of the SHA-256
compression function `F` as defined in FIPS 180-4 Section 6.2.2. This
is *not* the full SHA-256 hash: there is no padding, no length
encoding, no initial-value injection. The function takes a chaining
state `H` of 8 u32 words and a pre-parsed 64-byte message block as 16
u32 big-endian words, and returns the updated chaining state.

This is precisely the shape that Noir's `__sha256_compression`
foreign builtin exposes.

References:
- FIPS 180-4, "Secure Hash Standard":
  https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
  - §4.1.2 Ch / Maj / Σ_{0,1} / σ_{0,1} definitions for SHA-256
  - §4.2.2 K[0..63] round constants
  - §5.3.3 Initial hash value H(0)
  - §6.2.2 Hash computation (the compression we implement)

Validation: see `Lampe/Tests/Sha256.lean`. The vectors there are
copied verbatim from FIPS 180-2 "Secure Hash Standard" Appendix B —
both the single-block "abc" example (B.1) and the two-block
"abcdbcdec...mnopnopq" example (B.2), the latter giving us a
non-trivial intermediate compression-state target H^(1) as well as the
final hash H^(2).

  https://csrc.nist.gov/csrc/media/publications/fips/180/2/archive/
  2002-08-01/documents/fips180-2.pdf
-/

namespace Lampe.Crypto.Sha256

/-! ### Constants -/

/-- FIPS 180-4 §4.2.2: the 64 round constants K[0..63]. Each is the
first 32 bits of the fractional part of the cube root of the t-th
prime. -/
def roundConstants : List.Vector (BitVec 32) 64 :=
  ⟨[ 0x428a2f98#32, 0x71374491#32, 0xb5c0fbcf#32, 0xe9b5dba5#32,
     0x3956c25b#32, 0x59f111f1#32, 0x923f82a4#32, 0xab1c5ed5#32,
     0xd807aa98#32, 0x12835b01#32, 0x243185be#32, 0x550c7dc3#32,
     0x72be5d74#32, 0x80deb1fe#32, 0x9bdc06a7#32, 0xc19bf174#32,
     0xe49b69c1#32, 0xefbe4786#32, 0x0fc19dc6#32, 0x240ca1cc#32,
     0x2de92c6f#32, 0x4a7484aa#32, 0x5cb0a9dc#32, 0x76f988da#32,
     0x983e5152#32, 0xa831c66d#32, 0xb00327c8#32, 0xbf597fc7#32,
     0xc6e00bf3#32, 0xd5a79147#32, 0x06ca6351#32, 0x14292967#32,
     0x27b70a85#32, 0x2e1b2138#32, 0x4d2c6dfc#32, 0x53380d13#32,
     0x650a7354#32, 0x766a0abb#32, 0x81c2c92e#32, 0x92722c85#32,
     0xa2bfe8a1#32, 0xa81a664b#32, 0xc24b8b70#32, 0xc76c51a3#32,
     0xd192e819#32, 0xd6990624#32, 0xf40e3585#32, 0x106aa070#32,
     0x19a4c116#32, 0x1e376c08#32, 0x2748774c#32, 0x34b0bcb5#32,
     0x391c0cb3#32, 0x4ed8aa4a#32, 0x5b9cca4f#32, 0x682e6ff3#32,
     0x748f82ee#32, 0x78a5636f#32, 0x84c87814#32, 0x8cc70208#32,
     0x90befffa#32, 0xa4506ceb#32, 0xbef9a3f7#32, 0xc67178f2#32 ],
   by rfl⟩

/-- FIPS 180-4 §5.3.3: SHA-256 initial hash value `H(0)`. First 32
bits of the fractional parts of the square roots of the first 8
primes. The constant itself lives in `Lampe.Crypto.sha256IV` (it is
also the BLAKE2s/BLAKE3 IV); this re-exports it at the `List.Vector`
shape used by the test vectors. -/
def initialHash : List.Vector (BitVec 32) 8 :=
  ⟨sha256IV.toList, by rfl⟩

/-! ### Bit-mixing helpers (FIPS 180-4 §4.1.2)

`rotr32` is shared with the BLAKE models via
`Lampe.Crypto.WordUtils`. -/

/-- Logical right shift, expressed at the same arity as `rotr32` for
symmetry. -/
@[inline] def shr32 (x : BitVec 32) (n : Nat) : BitVec 32 := x >>> n

/-- FIPS 180-4 §4.1.2:
`Σ_0(x) = ROTR(x,2) ⊕ ROTR(x,13) ⊕ ROTR(x,22)`. -/
def bigSigma0 (x : BitVec 32) : BitVec 32 :=
  rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

/-- FIPS 180-4 §4.1.2:
`Σ_1(x) = ROTR(x,6) ⊕ ROTR(x,11) ⊕ ROTR(x,25)`. -/
def bigSigma1 (x : BitVec 32) : BitVec 32 :=
  rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

/-- FIPS 180-4 §4.1.2:
`σ_0(x) = ROTR(x,7) ⊕ ROTR(x,18) ⊕ SHR(x,3)`. -/
def smallSigma0 (x : BitVec 32) : BitVec 32 :=
  rotr32 x 7 ^^^ rotr32 x 18 ^^^ shr32 x 3

/-- FIPS 180-4 §4.1.2:
`σ_1(x) = ROTR(x,17) ⊕ ROTR(x,19) ⊕ SHR(x,10)`. -/
def smallSigma1 (x : BitVec 32) : BitVec 32 :=
  rotr32 x 17 ^^^ rotr32 x 19 ^^^ shr32 x 10

/-- FIPS 180-4 §4.1.2:
`Ch(x,y,z) = (x AND y) ⊕ ((NOT x) AND z)`. -/
def ch (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

/-- FIPS 180-4 §4.1.2:
`Maj(x,y,z) = (x AND y) ⊕ (x AND z) ⊕ (y AND z)`. -/
def maj (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-! ### Message schedule and round step -/

/-- FIPS 180-4 §6.2.2 step 1: extend the 16-word message block to the
64-word message schedule `W[0..63]`.

For `t ∈ [0, 16)`: `W[t] = M[t]`.
For `t ∈ [16, 64)`:
`W[t] = σ_1(W[t-2]) + W[t-7] + σ_0(W[t-15]) + W[t-16]`. -/
def messageSchedule
    (m : List.Vector (BitVec 32) 16) : List.Vector (BitVec 32) 64 := Id.run do
  let mut w : Array (BitVec 32) := Array.replicate 64 0
  for i in [:16] do
    w := w.set! i (m.toList.getD i 0)
  for t in [16:64] do
    let w2  := w[t - 2]!
    let w7  := w[t - 7]!
    let w15 := w[t - 15]!
    let w16 := w[t - 16]!
    w := w.set! t (smallSigma1 w2 + w7 + smallSigma0 w15 + w16)
  return List.Vector.ofFn (fun (i : Fin 64) => w.getD i.val 0)

/-- Working-variable bundle for a single SHA-256 round. -/
structure Vars where
  a : BitVec 32
  b : BitVec 32
  c : BitVec 32
  d : BitVec 32
  e : BitVec 32
  f : BitVec 32
  g : BitVec 32
  h : BitVec 32

/-- FIPS 180-4 §6.2.2 step 3: one round of the 64-round main loop.

Given working variables `a..h`, round constant `K[t]` and message
schedule word `W[t]`, compute the updated variables according to:

```
T1 = h + Σ_1(e) + Ch(e,f,g) + K[t] + W[t]
T2 = Σ_0(a) + Maj(a,b,c)
h ← g; g ← f; f ← e; e ← d + T1; d ← c; c ← b; b ← a; a ← T1 + T2.
``` -/
def roundStep (v : Vars) (kt wt : BitVec 32) : Vars :=
  let T1 := v.h + bigSigma1 v.e + ch v.e v.f v.g + kt + wt
  let T2 := bigSigma0 v.a + maj v.a v.b v.c
  { a := T1 + T2
    b := v.a
    c := v.b
    d := v.c
    e := v.d + T1
    f := v.e
    g := v.f
    h := v.g }

/-- FIPS 180-4 §6.2.2 step 2-4 main loop: run all 64 rounds starting
from working variables initialised to the input state. -/
def runRounds
    (initial : Vars) (w : List.Vector (BitVec 32) 64) : Vars := Id.run do
  let kArr := roundConstants.toList.toArray
  let wArr := w.toList.toArray
  let mut v := initial
  for t in [:64] do
    let kt := kArr[t]!
    let wt := wArr[t]!
    v := roundStep v kt wt
  return v

/-! ### Driver -/

/-- FIPS 180-4 §6.2.2: a single SHA-256 compression. Updates the
8-word chaining state `H` by absorbing one 16-word (64-byte) message
block `M`.

This matches Noir's `__sha256_compression` foreign builtin: the
caller is responsible for padding, length encoding, and any chaining
across multiple blocks. -/
def compressOne
    (state : List.Vector (BitVec 32) 8) (msg : List.Vector (BitVec 32) 16) :
    List.Vector (BitVec 32) 8 :=
  let w := messageSchedule msg
  let initial : Vars :=
    { a := state.get ⟨0, by omega⟩
      b := state.get ⟨1, by omega⟩
      c := state.get ⟨2, by omega⟩
      d := state.get ⟨3, by omega⟩
      e := state.get ⟨4, by omega⟩
      f := state.get ⟨5, by omega⟩
      g := state.get ⟨6, by omega⟩
      h := state.get ⟨7, by omega⟩ }
  let v := runRounds initial w
  ⟨[ state.get ⟨0, by omega⟩ + v.a,
     state.get ⟨1, by omega⟩ + v.b,
     state.get ⟨2, by omega⟩ + v.c,
     state.get ⟨3, by omega⟩ + v.d,
     state.get ⟨4, by omega⟩ + v.e,
     state.get ⟨5, by omega⟩ + v.f,
     state.get ⟨6, by omega⟩ + v.g,
     state.get ⟨7, by omega⟩ + v.h ],
   by rfl⟩

/-- Wrapper matching the Noir builtin signature shape:
`(state: [u32; 8], msg: [u32; 16]) → [u32; 8]`. -/
def compress
    {p : Prime}
    (state : Tp.denote p ((Tp.u 32).array (8 : U 32)))
    (msg   : Tp.denote p ((Tp.u 32).array (16 : U 32))) :
    Tp.denote p ((Tp.u 32).array (8 : U 32)) :=
  compressOne state msg

end Lampe.Crypto.Sha256
