import «std-1.0.0-beta.12».Extracted
import Lampe
import Stdlib.Field.Bn254

set_option maxRecDepth 4096

namespace Lampe.Stdlib.Hash.Mod

open Lampe
open «std-1.0.0-beta.12» (env)

abbrev from_field_unsafe := «std-1.0.0-beta.12::hash::from_field_unsafe»

theorem from_field_unsafe_spec {p} [Prime.BitsGT p 129] {scalar : Fp p} :
    STHoare p env ⟦⟧
      (from_field_unsafe.call h![] h![scalar])
      (fun (r : Fp p × Fp p × Unit) =>
        scalar = r.1 + (Stdlib.Field.Bn254.pow128 : Fp p) * r.2.1) := by
  enter_decl
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · apply STHoare.letIn_intro (Q := fun v₀ => ⟦v₀ = FuncRef.decl
        "«std-1.0.0-beta.12::field::bn254::decompose_hint»" [] h![]⟧)
    · apply STHoare.fn_intro
    · intro v₀
      apply Lampe.Steps.pluck_final_pure_destructively
      intro hv₀
      subst hv₀
      exact Stdlib.Field.Bn254.decompose_hint_intro
  · intro v₂
    steps [Stdlib.Field.Bn254.two_pow_128_spec]
    simp_all [beq_true, decide_eq_true_eq]

theorem unit_hash_spec {p H self state} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] .unit h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps

theorem field_hash_spec {p H self state}
    (h_write : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, self])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] .field h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write
  · intro; steps

theorem u8_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.u 8) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem u1_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.u 1) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem u16_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.u 16) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem u32_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.u 32) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem u64_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.u 64) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem u128_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.u 128) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem bool_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] .bool h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem i8_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.i 8) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem i16_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.i 16) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem i32_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.i 32) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

theorem i64_hash_spec {p H self state}
    (h_write : ∀ x : Fp p, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hasher».write h![] H h![] h![] h![state, x])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.i 64) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait; steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · exact h_write _
  · intro; steps

end Lampe.Stdlib.Hash.Mod
