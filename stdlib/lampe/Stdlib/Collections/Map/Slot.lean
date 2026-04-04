import Stdlib.Collections.Map.Core

namespace Lampe.Stdlib.Collections.Map

open «std-1.0.0-beta.14»

/-!
Hoare-logic specs for `collections::map::Slot` methods.

- `is_valid_spec`
- `is_available_spec`
- `set_spec`
- `mark_deleted_spec`
-/

theorem is_valid_spec {p K V s} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::Slot::is_valid».call h![K, V] h![s])
      (fun r => r = Slot.isValid s) := by
  enter_decl
  steps
  next => simpa [Slot.isValid, Slot.isDeleted, Slot.isPresent]
  next => exact ⟨⟩

theorem is_available_spec {p K V s} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::map::Slot::is_available».call h![K, V] h![s])
      (fun r => r = Slot.isAvailable s) := by
  enter_decl
  steps
  next => simpa [Slot.isAvailable, Slot.isDeleted, Slot.isPresent]
  next => exact ⟨⟩

theorem set_spec {p K V ref s key value} :
    STHoare p env
      ([ref ↦ ⟨slotTp K V, s⟩])
      («std-1.0.0-beta.14::collections::map::Slot::set».call h![K, V] h![ref, key, value])
      (fun _ => ∃∃ s',
        [ref ↦ ⟨slotTp K V, s'⟩] ⋆
        ⟦Slot.key s' = key ∧
         Slot.value s' = value ∧
         Slot.isPresent s' = true ∧
         Slot.isDeleted s' = false ∧
         Slot.isValid s' = true⟧) := by
  enter_decl
  steps <;> try exact ⟨⟩
  rcases s with ⟨sk, sv, sp, sd, ⟨⟩⟩
  simp only [Lens.modify, Lens.get, Access.modify, Access.get, Access.tuple,
    Option.some_bind, Option.bind_some,
    Builtin.replaceTuple'_tail, Builtin.replaceTuple'_head]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  unfold Slot.isValid Slot.isDeleted Slot.isPresent Builtin.indexTpl
  rfl

theorem mark_deleted_spec {p K V ref s} :
    STHoare p env
      ([ref ↦ ⟨slotTp K V, s⟩])
      («std-1.0.0-beta.14::collections::map::Slot::mark_deleted».call h![K, V] h![ref])
      (fun _ => ∃∃ s',
        [ref ↦ ⟨slotTp K V, s'⟩] ⋆
        ⟦Slot.key s' = Slot.key s ∧
         Slot.value s' = Slot.value s ∧
         Slot.isPresent s' = Slot.isPresent s ∧
         Slot.isDeleted s' = true ∧
         Slot.isValid s' = false⟧) := by
  enter_decl
  steps; try exact ⟨⟩
  rcases s with ⟨sk, sv, sp, sd, ⟨⟩⟩
  simp only [Lens.modify, Lens.get, Access.modify, Access.get, Access.tuple,
    Option.some_bind, Option.bind_some,
    Builtin.replaceTuple'_tail, Builtin.replaceTuple'_head]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  unfold Slot.isValid Slot.isDeleted Slot.isPresent Builtin.indexTpl
  rfl

end Lampe.Stdlib.Collections.Map
