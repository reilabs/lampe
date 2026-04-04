import «std-1.0.0-beta.14».Extracted
import Lampe

namespace Lampe.Stdlib.Hash.Poseidon2

open «std-1.0.0-beta.14»

/-!
Formalization of Noir's `std::hash::poseidon2` module.

## Types

- `Poseidon2`: sponge state with `cache: [Field; 3]`, `state: [Field; 4]`,
  `cache_size: u32`, `squeeze_mode: bool`
- `Poseidon2Hasher`: wrapper holding `Vector<Field>` of accumulated inputs

## Poseidon2 sponge methods

- `new(iv)`: initialize sponge with IV at `state[RATE]`
- `absorb(&mut self, input)`: absorb one field element
- `squeeze(&mut self)`: finalize and extract
- `perform_duplex(&mut self)`: internal permutation step
- `hash(input, message_size)`: one-shot hash
- `hash_internal(input, in_len, is_variable_length)`: core with padding

## Trait impls

- `Hasher for Poseidon2Hasher` (impl_0): `write` appends; `finish` builds sponge
- `Default for Poseidon2Hasher` (impl_1): empty vector
-/

/-! ## Type projections -/

section Poseidon2

abbrev spongeType : Tp :=
  «std-1.0.0-beta.14::hash::poseidon2::Poseidon2».tp h![]

abbrev SpongeDenote (p : Prime) := Tp.denote p spongeType

def RATE : U 32 := 3

def cache {p} (s : SpongeDenote p) : List.Vector (Fp p) 3 :=
  Builtin.indexTpl s Builtin.Member.head

def state {p} (s : SpongeDenote p) : List.Vector (Fp p) 4 :=
  Builtin.indexTpl s Builtin.Member.head.tail

def cacheSize {p} (s : SpongeDenote p) : U 32 :=
  Builtin.indexTpl s Builtin.Member.head.tail.tail

def squeezeMode {p} (s : SpongeDenote p) : Bool :=
  Builtin.indexTpl s Builtin.Member.head.tail.tail.tail

end Poseidon2

section Poseidon2Hasher

abbrev hasherType : Tp :=
  «std-1.0.0-beta.14::hash::poseidon2::Poseidon2Hasher».tp h![]

abbrev HasherDenote (p : Prime) := Tp.denote p hasherType

/-- Project the accumulated inputs as a list. The internal field is `Vector<Field>`. -/
def inputsList {p} (h : HasherDenote p) : List (Fp p) :=
  Builtin.indexTpl h Builtin.Member.head

end Poseidon2Hasher

/-! ## Sponge method specs -/

theorem new_spec {p iv} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::new».call h![] h![iv])
      (fun (r : SpongeDenote p) =>
        cacheSize r = 0 ∧ squeezeMode r = false) := by
  sorry

theorem absorb_spec {p ref s input}
    (hmode : squeezeMode s = false) :
    STHoare p env
      ([ref ↦ ⟨spongeType, s⟩])
      («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::absorb».call h![] h![ref, input])
      (fun _ => ∃∃ s',
        [ref ↦ ⟨spongeType, s'⟩] ⋆
        ⟦squeezeMode s' = false⟧) := by
  sorry

theorem squeeze_spec {p ref s}
    (hmode : squeezeMode s = false) :
    STHoare p env
      ([ref ↦ ⟨spongeType, s⟩])
      («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::squeeze».call h![] h![ref])
      (fun _ => ∃∃ s',
        [ref ↦ ⟨spongeType, s'⟩] ⋆
        ⟦squeezeMode s' = true⟧) := by
  sorry

theorem hash_spec {p N input message_size} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::hash».call h![N] h![input, message_size])
      (fun (_ : Fp p) => True) := by
  sorry

/-! ## Poseidon2Hasher trait specs -/

/-
TODO: Trait impl specs for `Poseidon2Hasher` require `resolve_trait` for:
- `Hasher::finish` (impl_0): builds sponge from accumulated vector, returns hash
- `Hasher::write` (impl_0): appends field element to internal vector
- `Default::default` (impl_1): creates hasher with empty vector
-/

end Lampe.Stdlib.Hash.Poseidon2
