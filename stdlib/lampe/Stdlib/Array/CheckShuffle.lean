import «std-1.0.0-beta.12».Extracted.Array.CheckShuffle
import «std-1.0.0-beta.12».Extracted.«std-1.0.0-beta.12»
import Lampe
import Stdlib.Cmp

namespace Lampe
namespace Stdlib

export «std-1.0.0-beta.12».Extracted (
  «std::array::check_shuffle::check_shuffle»
  Array.CheckShuffle.env
)

open «std-1.0.0-beta.12».Extracted

lemma get_cast : ∀{M}{α} {l : List α}{h : M = List.length l} {i : Fin M}, l.get (h ▸ i) = l[i.val]'(by cases i; apply lt_of_lt_of_eq (by assumption) h) := by
  intros
  simp
  congr
  · simp [*]
  · simp

lemma List.perm_of_index_bijection
    (f : Fin N → Fin N)
    (bij: Function.Bijective f) {l₁ l₂ : List α}
    (len₁ : l₁.length = N)
    (len₂ : l₂.length = N)
    (same_elems: ∀i, l₁.get (len₁ ▸ i) = l₂.get (len₂ ▸ (f i))) : List.Perm l₁ l₂ := by
  induction N generalizing l₁ l₂ with
  | zero => simp_all [List.eq_nil_of_length_eq_zero]
  | succ N ih =>
    rcases List.exists_cons_of_length_eq_add_one len₁ with ⟨h₁, l₁, rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at len₁
    have : List.Perm l₁ (l₂.eraseIdx (f 0).toNat) := by
      have f_succ_lt_of_not_lt_zero (i : Fin N) : ¬(f 0 < f i.succ) → f i.succ < f 0 := by
        intro h
        have := Fin.lt_or_eq_of_le (le_of_not_gt h)
        cases this
        · assumption
        · rename_i h
          cases bij.injective h
      let f' : (Fin N → Fin N) := fun i => if h: f 0 < f i.succ then (f i.succ).pred (Fin.ne_zero_of_lt h) else (f i.succ).castPred (Fin.ne_last_of_lt (f_succ_lt_of_not_lt_zero _ h))
      apply ih
      case f => exact f'
      case bij =>
        have : Function.Surjective f' := by
          intro v
          by_cases v.castSucc >= f 0
          · have := bij.surjective v.succ
            rcases this with ⟨is, eq⟩
            have : is ≠ 0 := by
              intro h
              apply_fun f at h
              rw [eq] at h
              apply Fin.ne_of_lt (a := f 0) (b := v.succ)
              · apply lt_of_le_of_lt
                · assumption
                · simp
              · simp [h]
            exists is.pred this
            have : f is > f 0 := by
              rw [eq]
              apply lt_of_le_of_lt
              assumption
              simp
            simp [f', this]
            simp [eq]
          · rename_i h'
            simp only [ge_iff_le, not_le, f'] at h'
            have := bij.surjective v.castSucc
            rcases this with ⟨is, eq⟩
            have : is ≠ 0 := by
              intro h
              apply_fun f at h
              rw [eq] at h
              rw [h] at h'
              exact lt_irrefl _ h'
            exists is.pred this
            rw [←eq] at h'
            simp [f', not_lt_of_gt h']
            simp [eq]
        have : Function.Injective f' := by
          apply this.injective_of_fintype
          apply Equiv.refl
        apply And.intro <;> assumption
      case same_elems =>
        intro i
        unfold f'
        rw [get_cast, get_cast]
        simp only [get_cast] at same_elems
        split
        · rw [List.getElem_eraseIdx_of_ge]
          · have := same_elems i.succ
            simp at this
            rw [this]
            congr
            have : (f i.succ).val ≠ 0 := by
              intro h
              simp only [Fin.lt_def, h] at *
              contradiction
            simp [*]
          · rename f 0 < _ => hp
            simp only [Fin.lt_def] at hp
            apply Nat.le_pred_of_lt
            exact hp
        · rw [List.getElem_eraseIdx_of_lt]
          · have := same_elems i.succ
            simp_all
          · simp
            apply lt_of_le_of_ne
            · apply le_of_not_gt
              assumption
            · intro h
              have := bij.injective h
              cases this
        · rw [List.length_eraseIdx_of_lt]
          · simp_all
          · rw [len₂]
            apply Fin.prop
        · assumption
    have t₁ : l₂ = (l₂.eraseIdx (f 0).toNat).insertIdx (f 0).toNat (l₂[(f 0).toNat]'(by rw [len₂]; apply Fin.prop)) := by
      rw [List.insertIdx_eraseIdx_getElem]
    have t₂ : h₁ :: l₁ = l₁.insertIdx 0 h₁ := by simp
    rw [t₁, t₂]
    have := same_elems 0
    rw [get_cast, get_cast] at this
    simp at this
    rw [this]
    apply List.Perm.insertIdx_of_le
    · simp
    · have : (f 0).toNat ≤ N := by
        apply Nat.le_of_lt_succ
        exact Fin.prop _
      apply le_trans this
      apply le_trans ?_ (List.le_length_eraseIdx _ _)
      rw [len₂]
      simp
    assumption

lemma get_index_spec: STHoare p env ⟦⟧
    («std::array::check_shuffle::__get_index».call h![N] h![indices, idx])
    (fun r => True) := by
  enter_decl
  steps

theorem check_shuffle_spec
    (h_eq : ∀(a b : T.denote p), STHoare p env ⟦⟧ («std::cmp::Eq».eq h![] T h![] h![] h![a, b]) fun r: Bool => ⟦r ↔ a = b⟧)
    : STHoare p env ⟦⟧
    («std::array::check_shuffle::check_shuffle».call h![T, N] h![lhs, rhs])
    (fun _ => List.Perm lhs.toList rhs.toList) := by
  enter_decl
  steps
  step_as (⟦⟧) (fun _ => ⟦⟧)
  · enter_decl; steps
  steps

  loop_inv nat fun i _ ilt => ∀(j : Fin i), ∃ix, (shuffle_indices.get ix).toNat = j.toNat
  · intro j; fin_cases j
  · simp
  · intro i _ ihp
    steps [get_index_spec]
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

  rename ∀_, ∃_, _ = _ => shuffle_indices_surj


  loop_inv nat fun i _ ilt => ∀(k : Fin i), lhs.get (k.castLE ilt) = rhs[(shuffle_indices.get $ k.castLE ilt).toNat]?
  · intro k
    fin_cases k
  · simp
  · intro i _ ilt
    steps [h_eq]

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
      simp only [Fin.castLE, Fin.val_last, ←idxDef]
      rename BitVec.toNat (Builtin.CastTp.cast idx) < _ => hp
      simp at hp
      simp only [hp, getElem?_pos, Option.some.injEq]
      subst expected
      rename List.Vector.get rhs _  = List.Vector.get lhs _ => hpeq
      rw [Eq.comm] at hpeq
      convert hpeq
      · simp
      · simp [GetElem.getElem]
    · simp_all

  steps

  rename ∀_, some _ = _ => same_elems

  simp only [Fin.castLE_refl, some_eq_getElem?_iff] at same_elems

  have indices_range : ∀ (i : Fin N.toNat), (shuffle_indices.get i).toNat < N.toNat := by
    intro i; exact (same_elems i).1

  let f (i : Fin N.toNat) := Fin.mk (shuffle_indices.get i).toNat (indices_range i)

  have f_surj: Function.Surjective f := by
    intro i
    unfold f
    have := shuffle_indices_surj i
    rcases this with ⟨v, veq⟩
    exists v
    apply Fin.eq_of_val_eq
    assumption

  have f_bij : Function.Bijective f := f_surj.bijective_of_finite

  have same_elems : ∀(i : Fin N.toNat), lhs.toList.get (List.Vector.toList_length _ ▸ i) = rhs.toList.get (List.Vector.toList_length _ ▸ f i) := by
    intro i
    have := same_elems i
    rcases this with ⟨_, eq⟩
    simp only [List.get_eq_getElem, Fin.coe_cast, List.Vector.getElem_def, List.Vector.get_eq_get_toList] at eq
    simp only [get_cast]
    rw [←eq]
    rfl

  exact List.perm_of_index_bijection f f_bij (List.Vector.toList_length _) (List.Vector.toList_length _) same_elems

/--
Shows that the shuffle check cannot succeed with the given inputs.
-/
example :
    STHoare p env ⟦⟧
      («std::array::check_shuffle::check_shuffle».call h![.u 8, 3] h![⟨[1, 2, 3], by simp⟩, ⟨[1, 2, 2], by simp⟩])
      (fun _ => False) := by
  steps [check_shuffle_spec]
  · simp_all
  intros
  apply u8_eq_spec

end Stdlib
end Lampe
