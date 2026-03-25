import «noir_sort-0.0.0».Extracted
import «check_shuffle-0.0.0»
import Stdlib.Cmp

open Lampe
open Lampe.Stdlib.Cmp

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 4096

theorem sort_u32_spec {p} (a b : U 32) :
    STHoare p «noir_sort-0.0.0».env ⟦⟧
      («noir_sort-0.0.0::test::sort_u32».call h![] h![a, b])
      (fun r : Bool => r = decide (a ≤ b)) := by
  enter_decl
  steps
  assumption

private lemma u32_check_shuffle_spec {p} {N : U 32}
    {lhs rhs : List.Vector (U 32) N.toNat} :
    STHoare p «noir_sort-0.0.0».env ⟦⟧
      («check_shuffle-0.0.0::check_shuffle».call h![.u 32, N] h![lhs, rhs])
      (fun _ => List.Perm lhs.toList rhs.toList) := by
  apply STHoare.is_mono (show «check_shuffle-0.0.0».env ⊆ «noir_sort-0.0.0».env from by
    solve_env_subset)
  apply check_shuffle_spec
  · resolve_trait bySearch
  · intro a b
    apply STHoare.is_mono (show «std-1.0.0-beta.14».env ⊆ «check_shuffle-0.0.0».env from by
      solve_env_subset)
    exact Eq.u32_eq_spec

theorem sort_via_u32_sorted_spec {p} (N : U 32) (hN : 0 < N.toNat)
    (input : List.Vector (U 32) N.toNat) :
    STHoare p «noir_sort-0.0.0».env ⟦⟧
      («noir_sort-0.0.0::sort_via».call h![.u 32, N]
        h![input, (FuncRef.decl «noir_sort-0.0.0::test::sort_u32».name [] h![])])
      (fun out : List.Vector (U 32) N.toNat =>
        List.Perm input.toList out.toList ∧
        ∀ i (hi : i + 1 < N.toNat), out.get ⟨i, by omega⟩ ≤ out.get ⟨i + 1, by omega⟩) := by
  enter_decl
  apply STHoare.letIn_intro (Q := fun (sorted : List.Vector (U 32) N.toNat) => ⟦True⟧)
  · steps
    enter_decl
    steps
  · intro sorted
    steps
    loop_inv nat fun k _ _ =>
      ⟦∀ j < k, sorted.toList[j]! ≤ sorted.toList[j + 1]!⟧
    · intro j hj; simp at hj
    · simp
    · intro k hlo hk
      steps [sort_u32_spec]
      rename_i _ hinv _ _ _ hdec _
      intro j hj
      by_cases hjk : j < k
      · exact hinv j hjk
      · have hjk_eq : j = k := by omega
        subst hjk_eq
        rename_i hv2 hv1 hv
        simp only [beq_iff_eq, decide_eq_true_eq, List.Vector.get_eq_get_toList,
                   List.get_eq_getElem, List.Vector.toList_length, Fin.coe_cast] at hdec hv2 hv1 hv
        simp [BitVec.ofNatLT, BitVec.toNat_add] at hdec hv2 hv1 hv
        simp only [Fin.val_add, Fin.val_mk, BitVec.val_toFin] at hdec hv
        -- hv'  has (j+1) via definitional equality (BitVec.toNat ↑1 = 1 by computation)
        have hv' : (j + 1) % 4294967296 < BitVec.toNat N := hv
        have hlt : j + 1 < BitVec.toNat N := by omega
        rw [getElem!_pos _ j (by simpa using hv2),
            getElem!_pos _ (j + 1) (by simp [List.Vector.toList_length]; exact hlt)]
        convert hdec using 2
        -- goal: j + 1 = (j + BitVec.toNat ↑1) % 4294967296
        -- BitVec.toNat ↑1 = 1 definitionally; use change to bypass omega's atom issue
        change j + 1 = (j + 1) % 4294967296
        omega
    steps
    apply STHoare.letIn_intro (Q := fun _ => ⟦List.Perm input.toList sorted.toList⟧)
    · convert u32_check_shuffle_spec using 3 <;> rfl
    · intro
      steps
      rename_i h1leN h02N hinv _ out _ hperm
      rw [hperm]
      constructor
      · exact out
      · intro i hi
        have h1N : 1 ≤ N.toNat := by
          simp [BitVec.le_def, BitVec.toNat_ofNat] at h1leN; exact h1leN
        have hNsub : BitVec.toNat (N - (1 : U 32)) = N.toNat - 1 := by
          simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
          have := N.isLt; omega
        have hlt : i < BitVec.toNat (N - (1 : U 32)) := by rw [hNsub]; omega
        have hle := hinv i hlt
        simp only [List.Vector.get_eq_get_toList, List.get_eq_getElem, Fin.coe_cast,
                   List.Vector.toList_length]
        rw [← getElem!_pos _ i (by simp [List.Vector.toList_length]; omega),
            ← getElem!_pos _ (i + 1) (by simp [List.Vector.toList_length]; omega)]
        exact hle
