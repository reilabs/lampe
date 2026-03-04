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

theorem tuple2_hash_spec {p A B H self state}
    {A_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] A}
    {B_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] B}
    (h_hash_a : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] A h![] h![H] h![self.1, state])
      (fun _ => ⟦⟧))
    (h_hash_b : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] B h![] h![H] h![self.2.1, state])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.tuple none [A, B]) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps [h_hash_a, h_hash_b]

theorem tuple3_hash_spec {p A B C H self state}
    {A_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] A}
    {B_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] B}
    {C_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] C}
    (h_hash_a : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] A h![] h![H] h![self.1, state])
      (fun _ => ⟦⟧))
    (h_hash_b : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] B h![] h![H] h![self.2.1, state])
      (fun _ => ⟦⟧))
    (h_hash_c : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] C h![] h![H] h![self.2.2.1, state])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.tuple none [A, B, C]) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps [h_hash_a, h_hash_b, h_hash_c]

theorem tuple4_hash_spec {p A B C D H self state}
    {A_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] A}
    {B_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] B}
    {C_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] C}
    {D_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] D}
    (h_hash_a : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] A h![] h![H] h![self.1, state])
      (fun _ => ⟦⟧))
    (h_hash_b : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] B h![] h![H] h![self.2.1, state])
      (fun _ => ⟦⟧))
    (h_hash_c : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] C h![] h![H] h![self.2.2.1, state])
      (fun _ => ⟦⟧))
    (h_hash_d : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] D h![] h![H] h![self.2.2.2.1, state])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.tuple none [A, B, C, D]) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps [h_hash_a, h_hash_b, h_hash_c, h_hash_d]

theorem tuple5_hash_spec {p A B C D E H self state}
    {A_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] A}
    {B_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] B}
    {C_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] C}
    {D_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] D}
    {E_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] E}
    (h_hash_a : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] A h![] h![H] h![self.1, state])
      (fun _ => ⟦⟧))
    (h_hash_b : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] B h![] h![H] h![self.2.1, state])
      (fun _ => ⟦⟧))
    (h_hash_c : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] C h![] h![H] h![self.2.2.1, state])
      (fun _ => ⟦⟧))
    (h_hash_d : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] D h![] h![H] h![self.2.2.2.1, state])
      (fun _ => ⟦⟧))
    (h_hash_e : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] E h![] h![H] h![self.2.2.2.2.1, state])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.tuple none [A, B, C, D, E]) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps [h_hash_a, h_hash_b, h_hash_c, h_hash_d, h_hash_e]

theorem build_hasher_default_spec {p H _self}
    {H_hasher : «std-1.0.0-beta.12::hash::Hasher».hasImpl env h![] H}
    {H_default : «std-1.0.0-beta.12::default::Default».hasImpl env h![] H}
    (h_default : STHoare p env ⟦⟧
      («std-1.0.0-beta.12::default::Default».default h![] H h![] h![] h![])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::BuildHasher».build_hasher h![]
        («std-1.0.0-beta.12::hash::BuildHasherDefault».tp h![H]) h![H] h![] h![_self])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps [h_default]

theorem default_build_hasher_default_spec {p H}
    {H_hasher : «std-1.0.0-beta.12::hash::Hasher».hasImpl env h![] H}
    {H_default : «std-1.0.0-beta.12::default::Default».hasImpl env h![] H} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::default::Default».default h![]
        («std-1.0.0-beta.12::hash::BuildHasherDefault».tp h![H]) h![] h![] h![])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps

theorem array_hash_spec {p N T H self state}
    {T_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] T}
    (h_hash_elem : ∀ (elem : Tp.denote p T), STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] T h![] h![H] h![elem, state])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.array T N) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps
  loop_inv nat (fun _ _ _ => ⟦⟧)
  · simp
  · intros; steps [h_hash_elem]
  · steps

theorem slice_hash_spec {p T H} {self : List (Tp.denote p T)} {state}
    {T_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] T}
    {u32_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] (.u 32)}
    (h_hash_len : ∀ (len : U 32), STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.u 32) h![] h![H] h![len, state])
      (fun _ => ⟦⟧))
    (h_hash_elem : ∀ (elem : Tp.denote p T), STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] T h![] h![H] h![elem, state])
      (fun _ => ⟦⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::hash::Hash».hash h![] (.slice T) h![] h![H] h![self, state])
      (fun _ => ⟦⟧) := by
  resolve_trait
  steps [h_hash_len]
  loop_inv nat (fun _ _ _ => ⟦⟧)
  · simp
  · intros; steps [h_hash_elem]
  · steps

end Lampe.Stdlib.Hash.Mod
