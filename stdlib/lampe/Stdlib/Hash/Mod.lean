import «std-1.0.0-beta.14».Extracted
import Lampe
import Stdlib.Default
import Stdlib.Hash.Poseidon2

namespace Lampe.Stdlib.Hash

open «std-1.0.0-beta.14»

abbrev BuildHasherDefaultTp (H : Tp) : Tp :=
  «std-1.0.0-beta.14::hash::BuildHasherDefault».tp h![H]

abbrev Hasher.hasImpl (env : Env) (tp : Tp) :=
  «std-1.0.0-beta.14::hash::Hasher».hasImpl env h![] tp

abbrev HashTrait.hasImpl (env : Env) (tp : Tp) :=
  «std-1.0.0-beta.14::hash::Hash».hasImpl env h![] tp

def buildHasherDefaultRepr {p H} : Tp.denote p (BuildHasherDefaultTp H) :=
  HList.toTuple p h![] (some «std-1.0.0-beta.14::hash::BuildHasherDefault».name)

theorem poseidon2_permutation4_spec {p}
    {input : Tp.denote p (Tp.field.array (4 : U 32))}
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.14::hash::poseidon2_permutation».call h![(4 : U 32)]
          h![input, (4 : U 32)])
        (fun r => r = Lampe.Crypto.Poseidon2.noirPermutation4 input) := by
  enter_decl
  steps [Lampe.Stdlib.Hash.Poseidon2.poseidon2_permutation_builtin_spec]
  assumption

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
        («std-1.0.0-beta.14::hash::BuildHasher».build_hasher
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
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![] h![stateRef, self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] .field h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u1_hash_spec {p H stateRef}
    {self : U 1}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 1) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.u 1) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u8_hash_spec {p H stateRef}
    {self : U 8}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 8) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.u 8) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u16_hash_spec {p H stateRef}
    {self : U 16}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 16) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.u 16) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u32_hash_spec {p H stateRef}
    {self : U 32}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 32) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.u 32) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u64_hash_spec {p H stateRef}
    {self : U 64}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 64) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.u 64) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem u128_hash_spec {p H stateRef}
    {self : U 128}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 128) .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.u 128) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem i8_hash_spec {p H stateRef}
    {self : Tp.denote p (.i 8)}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 8) .field _ p
          (@Builtin.CastTp.cast (.i 8) (.u 8) _ p self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.i 8) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem i16_hash_spec {p H stateRef}
    {self : Tp.denote p (.i 16)}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 16) .field _ p
          (@Builtin.CastTp.cast (.i 16) (.u 16) _ p self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.i 16) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem i32_hash_spec {p H stateRef}
    {self : Tp.denote p (.i 32)}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 32) .field _ p
          (@Builtin.CastTp.cast (.i 32) (.u 32) _ p self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.i 32) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem i64_hash_spec {p H stateRef}
    {self : Tp.denote p (.i 64)}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast (.u 64) .field _ p
          (@Builtin.CastTp.cast (.i 64) (.u 64) _ p self)])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] (.i 64) h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem bool_hash_spec {p H stateRef}
    {self : Bool}
    {state final : Tp.denote p H}
    {h_hasher : Hasher.hasImpl env H}
    (h_write_spec : STHoare p env
      [stateRef ↦ ⟨H, state⟩]
      («std-1.0.0-beta.14::hash::Hasher».write h![] H h![] h![]
        h![stateRef, @Builtin.CastTp.cast .bool .field _ p self])
      (fun _ => [stateRef ↦ ⟨H, final⟩]))
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] .bool h![] h![H] h![self, stateRef])
        (fun _ => [stateRef ↦ ⟨H, final⟩]) := by
  resolve_trait
  steps [h_write_spec]

theorem unit_hash_spec {p H stateRef}
    {state : Tp.denote p H}
    : STHoare p env
        [stateRef ↦ ⟨H, state⟩]
        («std-1.0.0-beta.14::hash::Hash».hash h![] .unit h![] h![H] h![(), stateRef])
        (fun _ => [stateRef ↦ ⟨H, state⟩]) := by
  resolve_trait
  steps
