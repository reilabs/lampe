
import «check_shuffle-0.0.0».Extracted
import Stdlib.Cmp
import Stdlib.Array.CheckShuffle

open Lampe
open «check_shuffle-0.0.0»
open Lampe.Stdlib.Cmp
open Lampe.Stdlib.Array.CheckShuffle

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 4096

private lemma get_index_spec {p} {N : U 32} {indices : List.Vector (U 32) N.toNat} {idx : U 32} :
    STHoare p «check_shuffle-0.0.0».env ⟦⟧
      («check_shuffle-0.0.0::__get_index».call h![N] h![indices, idx])
      (fun _ : U 32 => ⟦⟧) := by
  enter_decl
  steps

theorem check_shuffle_spec {p} {T : Tp} {N : U 32}
    {lhs rhs : List.Vector (Tp.denote p T) N.toNat}
    (t_eq : Eq.hasImpl «check_shuffle-0.0.0».env T)
    (t_eq_spec : ∀ a b, STHoare p «check_shuffle-0.0.0».env ⟦⟧
        (Eq.eq h![] T h![] h![] h![a, b]) fun r : Bool => ⟦r ↔ a = b⟧) :
    STHoare p «check_shuffle-0.0.0».env ⟦⟧
      («check_shuffle-0.0.0::check_shuffle».call h![T, N] h![lhs, rhs])
      (fun _ => List.Perm lhs.toList rhs.toList) := by
  enter_decl
  steps
  apply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  · steps; enter_decl; steps
  · intro shuffle_indices
    steps
    loop_inv nat fun i _ ilt => ∀ (j : Fin i), ∃ ix, (shuffle_indices.get ix).toNat = j.toNat
    · intro j; fin_cases j
    · simp
    · intro i _ ihp
      apply STHoare.letIn_intro
        (Q := fun _ => ⟦∀ (j : Fin i), ∃ ix, (shuffle_indices.get ix).toNat = j.toNat⟧)
      · apply STHoare.consequence_frame
          (H₁ := ⟦⟧)
          (P := ⟦∀ (j : Fin i), ∃ ix, (shuffle_indices.get ix).toNat = j.toNat⟧)
          (Q₁ := fun _ => ⟦⟧)
        · steps; enter_decl; steps
        · rw [SLP.star_comm, SLP.star_true]; exact STHoare.SLP.entails_of_eq rfl
        · intro; rw [SLP.star_comm, SLP.star_true]; exact SLP.ent_star_top
      · intro idx
        steps
        intro j
        cases j using Fin.lastCases
        · rename _ = true => hp
          simp at hp
          generalize_proofs at hp
          exists ⟨idx.toNat, by assumption⟩
          rw [hp]
          rfl
        · apply_assumption
    steps
    rename ∀ _, ∃ _, _ = _ => shuffle_indices_surj
    loop_inv nat fun i _ ilt => ∀ (k : Fin i), lhs.get (k.castLE ilt) = rhs[(shuffle_indices.get $ k.castLE ilt).toNat]?
    · intro k; fin_cases k
    · simp
    · intro i _ ilt
      steps [t_eq_spec]
      rename (_ == true) = true => hp1
      simp only [beq_true] at hp1
      cases hp1
      rename (_ = _ ↔ _) => hp
      simp only [true_iff] at hp
      cases hp
      intro k
      cases k using Fin.lastCases
      · rename idx = _ => idxDef
        simp at idxDef
        simp only [Fin.castLE, Fin.val_last, ← idxDef]
        rename BitVec.toNat (Builtin.CastTp.cast idx) < _ => hp
        simp at hp
        simp only [hp, getElem?_pos, Option.some.injEq]
        subst expected
        rename List.Vector.get rhs _ = List.Vector.get lhs _ => hpeq
        rw [Eq.comm] at hpeq
        convert hpeq
      · simp_all
    steps
    rename ∀ _, some _ = _ => same_elems
    simp only [Fin.castLE_refl, some_eq_getElem?_iff] at same_elems
    have indices_range : ∀ (i : Fin N.toNat), (shuffle_indices.get i).toNat < N.toNat := by
      intro i; exact (same_elems i).1
    let f (i : Fin N.toNat) := Fin.mk (shuffle_indices.get i).toNat (indices_range i)
    have f_surj : Function.Surjective f := by
      intro i
      unfold f
      have := shuffle_indices_surj i
      rcases this with ⟨v, veq⟩
      exists v
      apply Fin.eq_of_val_eq
      assumption
    have f_bij : Function.Bijective f := f_surj.bijective_of_finite
    have same_elems : ∀ (i : Fin N.toNat),
        lhs.toList.get (List.Vector.toList_length _ ▸ i) =
        rhs.toList.get (List.Vector.toList_length _ ▸ f i) := by
      intro i
      have := same_elems i
      rcases this with ⟨_, eq⟩
      simp only [List.get_eq_getElem, Fin.coe_cast, List.Vector.getElem_def,
                 List.Vector.get_eq_get_toList] at eq
      simp only [get_cast]
      rw [← eq]
      rfl
    exact List.perm_of_index_bijection f f_bij
      (List.Vector.toList_length _) (List.Vector.toList_length _) same_elems
