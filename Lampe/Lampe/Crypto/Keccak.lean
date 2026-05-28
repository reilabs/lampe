import Lampe.Tp

/-!
# Keccak-f[1600] — concrete reference semantics (FIPS 202)

A computable Lean 4 implementation of the Keccak-f[1600] permutation,
matching the FIPS 202 specification. State is 25 lanes of 64 bits,
indexed as a 5×5 matrix `state[x, y] = state[x + 5 * y]`.

The implementation is "direct" — `keccakF1600` is defined inline as
24 iterations of the round function. We avoid Verity's
Tracer-monad / pre-unrolled `Instr`-list trick because Lampe's use
case is symbolic (specs of the form `r = keccakF1600 input`) and
test-vector validation via `native_decide`, neither of which requires
the kernel to unfold 24 rounds at elaboration time.

If a future caller needs `by decide` on a concrete Keccak input and
hits an elaborator memory limit, the fallback is the Verity approach:
pre-unrolling 24 rounds into a generated data file (see
`lfglabs-dev/verity/Compiler/Keccak/Circuit.lean`).

This is Keccak-f[1600], the underlying permutation. It is **identical
between FIPS 202 SHA-3 and Ethereum's keccak256** — the two differ
only in the sponge-layer padding byte (`0x06` vs `0x01`), which
appears at higher levels of the call stack, not in this function.

References:
- FIPS 202: SHA-3 Standard, Section 3.2 (Keccak-p)
- https://keccak.team/files/Keccak-reference-3.0.pdf
-/

namespace Lampe.Crypto.Keccak

/-! ### Constants -/

/-- The 24 Keccak-f[1600] round constants (FIPS 202 Table 4). -/
def roundConstants : List.Vector (BitVec 64) 24 :=
  ⟨[0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808a#64,
    0x8000000080008000#64, 0x000000000000808b#64, 0x0000000080000001#64,
    0x8000000080008081#64, 0x8000000000008009#64, 0x000000000000008a#64,
    0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000a#64,
    0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64,
    0x8000000000008003#64, 0x8000000000008002#64, 0x8000000000000080#64,
    0x000000000000800a#64, 0x800000008000000a#64, 0x8000000080008081#64,
    0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64], rfl⟩

/-- Per-lane rotation offsets for the ρ step (FIPS 202 Table 2),
flattened to `offset[x + 5 * y]`. -/
def rotationOffsets : List.Vector Nat 25 :=
  ⟨[ 0,  1, 62, 28, 27,
    36, 44,  6, 55, 20,
     3, 10, 43, 25, 39,
    41, 45, 15, 21,  8,
    18,  2, 61, 56, 14], rfl⟩

/-! ### State accessors

The state is `List.Vector (BitVec 64) 25`. We use lightweight helpers
for `Fin 5 × Fin 5`-coordinate access; index bounds discharge by
`omega`. -/

/-- Index a lane by `(x, y) : Fin 5 × Fin 5`. -/
@[inline] def laneIdx (x y : Fin 5) : Fin 25 :=
  ⟨x.val + 5 * y.val, by have := x.isLt; have := y.isLt; omega⟩

@[inline] def State : Type := List.Vector (BitVec 64) 25

/-! ### Round steps -/

/-- The θ step. -/
def theta (a : State) : State :=
  -- c[x] = XOR over y of a[x + 5y]
  let c : List.Vector (BitVec 64) 5 := List.Vector.ofFn fun (x : Fin 5) =>
    a.get (laneIdx x ⟨0, by decide⟩) ^^^
    a.get (laneIdx x ⟨1, by decide⟩) ^^^
    a.get (laneIdx x ⟨2, by decide⟩) ^^^
    a.get (laneIdx x ⟨3, by decide⟩) ^^^
    a.get (laneIdx x ⟨4, by decide⟩)
  -- d[x] = c[x-1] XOR rot(c[x+1], 1)
  let d : List.Vector (BitVec 64) 5 := List.Vector.ofFn fun (x : Fin 5) =>
    c.get ⟨(x.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ ^^^
    (c.get ⟨(x.val + 1) % 5, Nat.mod_lt _ (by decide)⟩).rotateLeft 1
  -- Apply: a[x + 5y] XOR d[x]
  List.Vector.ofFn fun (i : Fin 25) =>
    let x : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
    a.get i ^^^ d.get x

/-- The combined ρ ∘ π step. -/
def rhoPi (a : State) : State :=
  List.Vector.ofFn fun (i : Fin 25) =>
    let x : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
    let y : Fin 5 := ⟨i.val / 5, by
      have h := i.isLt
      omega⟩
    -- π: source coordinates (x', y') = (y, (2x + 3y) mod 5)
    -- equivalently a'[x, y] = rot(a[(x + 3y) mod 5 + 5x], offset)
    let srcX : Fin 5 := ⟨(x.val + 3 * y.val) % 5, Nat.mod_lt _ (by decide)⟩
    let srcIdx : Fin 25 := laneIdx srcX x
    let rot := rotationOffsets.get srcIdx
    (a.get srcIdx).rotateLeft rot

/-- The χ step (nonlinear S-box across each row). -/
def chi (a : State) : State :=
  List.Vector.ofFn fun (i : Fin 25) =>
    let x : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
    let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
    let nx1 : Fin 5 := ⟨(x.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
    let nx2 : Fin 5 := ⟨(x.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
    a.get i ^^^ (~~~(a.get (laneIdx nx1 y)) &&& a.get (laneIdx nx2 y))

/-- The ι step: XOR the round constant into lane 0. -/
def iota (a : State) (round : Fin 24) : State :=
  a.set ⟨0, by decide⟩ (a.get ⟨0, by decide⟩ ^^^ roundConstants.get round)

/-- One Keccak-p round: θ → ρ → π → χ → ι. -/
def keccakRound (a : State) (round : Fin 24) : State :=
  iota (chi (rhoPi (theta a))) round

/-- Keccak-f[1600]: 24 rounds of `keccakRound`. -/
def keccakF1600State (a : State) : State :=
  (List.finRange 24).foldl keccakRound a

/-! ### Entry point matching the builtin descriptor -/

/-- Concrete Keccak-f[1600] over the Lampe state shape. Matches the
opaque signature the builtin descriptor uses. -/
def keccakF1600 {p : Prime}
    (input : Tp.denote p ((Tp.u 64).array (25 : U 32))) :
    Tp.denote p ((Tp.u 64).array (25 : U 32)) :=
  keccakF1600State input

end Lampe.Crypto.Keccak
