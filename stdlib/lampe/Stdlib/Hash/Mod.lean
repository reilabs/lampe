import «std-1.0.0-beta.25».Extracted
import Lampe
import Stdlib.Default
import Stdlib.Hash.Poseidon2

namespace Lampe.Stdlib.Hash

open «std-1.0.0-beta.25»

abbrev BuildHasherDefaultTp (H : Tp) : Tp :=
  «std-1.0.0-beta.25::hash::BuildHasherDefault».tp h![H]

abbrev Hasher.hasImpl (env : Env) (tp : Tp) :=
  «std-1.0.0-beta.25::hash::Hasher».hasImpl env h![] tp

abbrev HashTrait.hasImpl (env : Env) (tp : Tp) :=
  «std-1.0.0-beta.25::hash::Hash».hasImpl env h![] tp

def buildHasherDefaultRepr {p H} : Tp.denote p (BuildHasherDefaultTp H) :=
  HList.toTuple p h![] (some «std-1.0.0-beta.25::hash::BuildHasherDefault».name)

theorem poseidon2_permutation4_spec {p}
    {input : Tp.denote p (Tp.field.array (4 : U 32))}
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.25::hash::poseidon2_permutation».call h![(4 : U 32)]
          h![input])
        (fun r => r = Lampe.Crypto.Poseidon2.noirPermutation4 input) := by
  enter_decl
  steps [Lampe.Stdlib.Hash.Poseidon2.config_state_size_spec,
    Lampe.Stdlib.Hash.Poseidon2.poseidon2_permutation_builtin_spec]
  · assumption
  all_goals simp_all

/-- Spec for the `sha256_compression` foreign builtin: returns the
concrete `Crypto.Sha256.compressOne` round-function output for the
given 8-word chaining state and 16-word message block.

The Noir signature is `(input: [u32; 16], state: [u32; 8]) -> [u32; 8]`
whereas the builtin descriptor takes `(state, msg)`; the underlying
`callBuiltin` therefore receives the two arrays in `(state, msg)`
order, matching `compressOne state msg`. -/
theorem sha256_compression_builtin_spec {p}
    {state : Tp.denote p ((Tp.u 32).array (8 : U 32))}
    {msg : Tp.denote p ((Tp.u 32).array (16 : U 32))} :
    STHoare p env ⟦⟧
      (.callBuiltin [(Tp.u 32).array (8 : U 32), (Tp.u 32).array (16 : U 32)]
        ((Tp.u 32).array (8 : U 32))
        Builtin.sha256Compression h![state, msg])
      (fun r => r = Lampe.Crypto.Sha256.compressOne state msg) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.sha256Compression rfl () p env
    h![state, msg]

/-- Spec for the `blake2s` foreign builtin: returns the concrete
RFC 7693 BLAKE2s-256 32-byte digest of the length-`N` input. -/
theorem blake2s_builtin_spec {p} {N : U 32}
    {input : Tp.denote p ((Tp.u 8).array N)} :
    STHoare p env ⟦⟧
      (.callBuiltin [(Tp.u 8).array N] ((Tp.u 8).array (32 : U 32))
        Builtin.blake2S h![input])
      (fun r => r = Lampe.Crypto.Blake2s.blake2sHash input) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.blake2S rfl N p env h![input]

theorem blake3_builtin_spec {p} {N : U 32}
    {input : Tp.denote p ((Tp.u 8).array N)} :
    STHoare p env ⟦⟧
      (.callBuiltin [(Tp.u 8).array N] ((Tp.u 8).array (32 : U 32))
        Builtin.blake3 h![input])
      (fun r => r = Lampe.Crypto.Blake3.blake3Hash input) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.blake3 rfl N p env h![input]

/-- Spec for `hash::blake3<N>`: returns the concrete BLAKE3 32-byte
digest of the length-`N` input. The Noir wrapper has an
`is_unconstrained`-guarded `static_assert` on `N ≤ 1024`; under Lampe's
`isUnconstrained = false`, that branch is unreachable and the wrapper
reduces to the builtin call. -/
theorem blake3_spec {p} {N : U 32}
    {input : Tp.denote p ((Tp.u 8).array N)} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::blake3».call h![N] h![input])
      (fun r => r = Lampe.Crypto.Blake3.blake3Hash input) := by
  enter_decl
  -- Reduce `isUnconstrained()` (always `false`); the body becomes
  -- `letIn (ite false ...) (fun _ => blake3 input)`.
  steps
  all_goals (try exact ())
  apply STHoare.letIn_intro (Q := fun _ => ⟦True⟧)
  · apply STHoare.ite_intro_of_false rfl
    steps
  · intro _
    steps [blake3_builtin_spec]
    assumption

/-- Spec for the `keccakf1600` foreign builtin: returns the concrete
`Crypto.Keccak.keccakF1600` permutation of the 25 `u64` input lanes. -/
theorem keccakf1600_builtin_spec {p}
    {input : Tp.denote p ((Tp.u 64).array (25 : U 32))} :
    STHoare p env ⟦⟧
      (.callBuiltin [(Tp.u 64).array (25 : U 32)] ((Tp.u 64).array (25 : U 32))
        Builtin.keccakf1600 h![input])
      (fun r => r = Lampe.Crypto.Keccak.keccakF1600 input) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.keccakf1600 rfl () p env h![input]

theorem buildHasherDefault_default_spec {p H}
    {h_hasher : Hasher.hasImpl env H}
    {h_default : Default.hasDefaultImpl env H}
    : STHoare p env ⟦⟧
        (Lampe.Stdlib.Default.default h![] (BuildHasherDefaultTp H) h![] h![] h![])
        (fun r => r = buildHasherDefaultRepr (H := H)) := by
  resolve_trait
  steps
  simp [buildHasherDefaultRepr, *]

theorem buildHasherDefault_build_hasher_spec {p H}
    {h_hasher : Hasher.hasImpl env H}
    {h_default : Default.hasDefaultImpl env H}
    {h : Tp.denote p H}
    (h_default_spec : STHoare p env ⟦⟧
      (Lampe.Stdlib.Default.default h![] H h![] h![] h![])
      (fun r => r = h))
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.25::hash::BuildHasher».build_hasher
          h![] (BuildHasherDefaultTp H) h![H] h![] h![buildHasherDefaultRepr (H := H)])
        (fun r => r = h) := by
  resolve_trait
  steps [h_default_spec]
  assumption

theorem field_hash_spec {p H stateRef}
    {self : Fp p}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![] h![stateRef, self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] .field h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

-- Note: `u1` was removed in Noir 1.0.0-beta.25, so the corresponding `u1_hash_spec` is gone.

theorem u8_hash_spec {p H stateRef}
    {self : U 8}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 8) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.u 8) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u16_hash_spec {p H stateRef}
    {self : U 16}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 16) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.u 16) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u32_hash_spec {p H stateRef}
    {self : U 32}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 32) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.u 32) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u64_hash_spec {p H stateRef}
    {self : U 64}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 64) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.u 64) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u128_hash_spec {p H stateRef}
    {self : U 128}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 128) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.u 128) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem i8_hash_spec {p H stateRef}
    {self : Tp.denote p (.i 8)}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 8) .field _ p
          (@Builtin.CastTp.cast (.i 8) (.u 8) _ p self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.i 8) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem i16_hash_spec {p H stateRef}
    {self : Tp.denote p (.i 16)}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 16) .field _ p
          (@Builtin.CastTp.cast (.i 16) (.u 16) _ p self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.i 16) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem i32_hash_spec {p H stateRef}
    {self : Tp.denote p (.i 32)}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 32) .field _ p
          (@Builtin.CastTp.cast (.i 32) (.u 32) _ p self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.i 32) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem i64_hash_spec {p H stateRef}
    {self : Tp.denote p (.i 64)}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 64) .field _ p
          (@Builtin.CastTp.cast (.i 64) (.u 64) _ p self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] (.i 64) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem bool_hash_spec {p H stateRef}
    {self : Bool}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.25::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast .bool .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] .bool h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem unit_hash_spec {p H stateRef}
    {state : Tp.denote p H}
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.25::hash::Hash».hash h![] .unit h![] h![H] h![(), stateRef])
        (fun _ => [stateRef ↦ ⟨H, state⟩]) := by
  resolve_trait
  steps
