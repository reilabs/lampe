import Lampe.Data.Field
import Lampe.Crypto.Poseidon2.BN254T4

namespace Lampe.Crypto.Poseidon2

/--
Parameters for a Poseidon2 sponge.

The permutation is intentionally a parameter. Noir exposes Poseidon2 to the standard library as a
foreign permutation builtin, while the stdlib implements the cached additive sponge around it.
-/
structure Params (F : Type) where
  rate : Nat
  width : Nat
  rate_pos : 0 < rate
  rate_lt_width : rate < width
  permute : List.Vector F width → List.Vector F width

structure Sponge (F : Type) (params : Params F) where
  cache : List.Vector F params.rate
  state : List.Vector F params.width
  cacheSize : Nat
  squeezeMode : Bool

namespace Sponge

variable {F : Type} (params : Params F)

def zeroVector [OfNat F 0] (n : Nat) : List.Vector F n :=
  List.Vector.replicate n 0

def init [OfNat F 0] (iv : F) : Sponge F params where
  cache := zeroVector params.rate
  state := (zeroVector params.width).set ⟨params.rate, params.rate_lt_width⟩ iv
  cacheSize := 0
  squeezeMode := false

def addCacheToState [Add F] (s : Sponge F params) : List.Vector F params.width :=
  List.Vector.ofFn fun i =>
    if hRate : i.val < params.rate then
      if i.val < s.cacheSize then
        s.state.get i + s.cache.get ⟨i.val, hRate⟩
      else
        s.state.get i
    else
      s.state.get i

def performDuplex [Add F] (s : Sponge F params) : Sponge F params :=
  { s with state := params.permute (addCacheToState params s) }

def absorb? [Add F] (s : Sponge F params) (input : F) : Option (Sponge F params) :=
  if s.squeezeMode then
    none
  else if s.cacheSize = params.rate then
    let s' := performDuplex params s
    some { s' with
      cache := s'.cache.set ⟨0, params.rate_pos⟩ input
      cacheSize := 1
    }
  else if hSpace : s.cacheSize < params.rate then
    some { s with
      cache := s.cache.set ⟨s.cacheSize, hSpace⟩ input
      cacheSize := s.cacheSize + 1
    }
  else
    none

def squeeze? [Add F] (s : Sponge F params) : Option (F × Sponge F params) :=
  if s.squeezeMode then
    none
  else
    let s' := performDuplex params s
    let width_pos : 0 < params.width := Nat.lt_trans params.rate_pos params.rate_lt_width
    some (s'.state.get ⟨0, width_pos⟩, { s' with squeezeMode := true })

def absorbPrefix? [Add F] :
    Sponge F params → List F → Nat → Option (Sponge F params)
  | s, [], _ => some s
  | s, _ :: _, 0 => some s
  | s, x :: xs, n + 1 => do
      let s' ← absorb? params s x
      absorbPrefix? s' xs n

def hashWithIV? [OfNat F 0] [OfNat F 1] [Add F]
    (input : List F) (inLen : Nat) (isVariableLength : Bool) (iv : F) : Option F := do
  let sponge ← absorbPrefix? params (init params iv) input inLen
  let sponge ← if isVariableLength then absorb? params sponge 1 else some sponge
  let (out, _) ← squeeze? params sponge
  pure out

def noirIV [NatCast F] [Mul F] (inLen : Nat) : F :=
  (inLen : F) * (((2 : Nat) ^ 64 : Nat) : F)

def hash? [OfNat F 0] [OfNat F 1] [NatCast F] [Add F] [Mul F]
    (input : List F) (inLen : Nat) (isVariableLength : Bool) : Option F :=
  hashWithIV? params input inLen isVariableLength (noirIV inLen)

end Sponge

/-- Noir/TACEO BN254 width-4 Poseidon2 permutation, lifted to Lampe field semantics. -/
def noirPermutation4 {p : Prime} (state : List.Vector (Fp p) 4) : List.Vector (Fp p) 4 :=
  BN254T4.permutation state

def bn254T4Params (F : Type) [NatCast F] [Add F] [Mul F] : Params F where
  rate := 3
  width := 4
  rate_pos := by decide
  rate_lt_width := by decide
  permute := BN254T4.permutation

def noirParams4 (p : Prime) : Params (Fp p) where
  rate := 3
  width := 4
  rate_pos := by decide
  rate_lt_width := by decide
  permute := noirPermutation4

def noirHash? {p : Prime} (input : List (Fp p)) (inLen : Nat) (isVariableLength : Bool) :
    Option (Fp p) :=
  Sponge.hash? (noirParams4 p) input inLen isVariableLength

end Lampe.Crypto.Poseidon2
