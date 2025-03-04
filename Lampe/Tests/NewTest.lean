import Lampe

open Lampe

nr_def aaa<>(x : u8, n : u8) -> u8 {
    let mut a = x;
    for _? in (0 : u8) .. n {
        a = #uAdd(a, 1 : u8) : u8
    };
    a
}

nr_def «asdf»<>() -> [u8; 5] {
    let mut x = [0 : u8 ; 5];
    for i in 0 : u8 .. 5 : u8 {
            x[#cast(i) : u32] = #uAdd(i, 7 : u8) : u8;
    }
    ;
    x;
}

#check Tp.denote

lemma SLP.pure_star_iff_and [LawfulHeap α] {H : SLP α} : (⟦P⟧ ⋆ H) st ↔ P ∧ H st := by
  simp [SLP.star, SLP.lift]
  apply Iff.intro
  · rintro ⟨st₁, st₂, hdis, hst, ⟨hp, rfl⟩, hH⟩
    simp only [LawfulHeap.empty_union] at hst
    cases hst
    simp_all
  · intro ⟨hP, hH⟩
    exists ∅, st
    simp_all

lemma STHoare.pure_left_of_imp (h : P → STHoare lp Γ ⟦P⟧ E Q): STHoare lp Γ ⟦P⟧ E Q := by
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

-- lemma STHoare.exists_left_of_imp (h : P → STHoare lp Γ ⟦P⟧ E Q)
--     : STHoare lp Γ (SLP.exists' fun h => ⟦P⟧) E Q := by
--   sorry

lemma STHoare.pure_left {E : Expr (Tp.denote lp) tp} {Γ P Q} : (P → STHoare lp Γ ⟦True⟧ E Q) → STHoare lp Γ ⟦P⟧ E Q := by
  intro h
  apply STHoare.pure_left_of_imp
  intro
  apply STHoare.consequence (h_hoare := h (by assumption))
  · simp [SLP.lift, SLP.entails]
  · intro; apply SLP.entails_self

lemma STHoare.pure_left_nontriv {E : Expr (Tp.denote lp) tp} {Γ P Q}
    : (P → STHoare lp Γ H E Q) → STHoare lp Γ (⟦P⟧ ⋆ H) E Q := by
  intro h
  simp_all only [STHoare, THoare, SLP.star_assoc, SLP.pure_star_iff_and, implies_true]


def loopInvAux (u : U 8) : List.Vector (U 8) 5 :=
  let asdf := List.range' 7 u.toNat |>.take 5 |>.map (BitVec.ofNat 8 ·)
  let asdf2 : List (U 8) := asdf ++ (List.replicate (5 - asdf.length) 0)
  have : asdf2.length = 5 := by
    simp [asdf2, asdf]
  ⟨asdf2, this⟩

theorem loopInvAux_induction :
    (loopInvAux x).set x.toNat (x + 7#8) = loopInvAux (x + 1#8) := by
  sorry


-- theorem loopInvAux_induction2 :
--   List.Vector.eraseIdx 0 ((loopInvAux 0).insertIdx 1 1) =
--   loopInvAux 1 := by
--   unfold loopInvAux
--   ext i t
--   fin_cases i <;> simp <;> rfl

open STHoare
example : STHoare p Γ ⟦⟧ (asdf.fn.body _ h![] |>.body h![]) fun
    v => v = ⟨[7, 8, 9, 10, 11], by simp⟩ := by
  simp only [asdf]

  apply letIn_intro
  apply litU_intro
  intro v; apply pure_left; rintro rfl

  apply letIn_intro
  apply mkArray_intro
  simp

  intro v;
  apply pure_left; simp; rintro rfl

  apply letIn_intro
  apply ref_intro'
  intro v; simp

  apply letIn_intro
  apply consequence_frame_left; apply litU_intro
  simp; exact SLP.entails_self
  intro v; apply pure_left_nontriv; rintro rfl

  apply letIn_intro
  apply consequence_frame_left litU_intro
  simp; exact SLP.entails_self
  intro v; apply pure_left_nontriv; rintro rfl

  apply letIn_intro
  apply STHoare.consequence_frame_left (STHoare.loop_inv_intro
      (fun u _ _ => [v ↦ ⟨Tp.array (Tp.u 8) 5, loopInvAux u⟩])
      (fun x hlo hhi => ?_))
  · simp
    sl
    change 0 ≤ 5
    decide
  · simp
    apply letIn_intro
    apply consequence_frame_left litU_intro
    · simp; exact SLP.entails_self
    intro v; apply pure_left_nontriv; rintro rfl

    apply letIn_intro
    apply consequence_frame_left uAdd_intro
    · simp; exact SLP.entails_self
    intro v; apply pure_left_nontriv; simp; intro h; rintro rfl

    apply letIn_intro
    apply consequence_frame_left cast_intro
    simp; exact SLP.entails_self
    intro vv

    apply letIn_intro
    apply consequence_frame_left modifyLens_intro
    nth_rewrite 1 [SLP.star_comm]
    exact SLP.entails_self
    intro vvv

    apply ramified_frame_top var_intro
    simp
    sl
    congr
    simp [Access.modify]
    simp [Builtin.replaceArray']
    ext x
    fin_cases x <;> congr <;> sorry

  intro unt; apply letIn_intro
  apply consequence_frame_left readRef_intro
  simp; sl
  intro v; simp; apply pure_left_nontriv; rintro rfl
  rw [SLP.star_comm]
  apply pure_left_nontriv; intro h -- h is a weird hypothesis that isn't necessary

  apply ramified_frame_top var_intro
  sl
  simp_all
  rfl

def addOne (u : U 8) : U 8 := u + 1

def asdff (n : Nat) := Nat.repeat addOne n

def thm : Nat.repeat addOne n u = u + n := by
  sorry

example (h : x < 100) (hn : n < 100)
    : STHoare p Γ ⟦⟧ (aaa.fn.body _ h![] |>.body h![x, n]) fun v => v = x + n := by
  simp only [aaa]
  steps
  rename_i a b
  loop_inv fun u _ _ => [a ↦ ⟨Tp.u 8, Nat.repeat addOne u.toNat x⟩]
  · intros i hl hu
    steps
    congr
    rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    subst_vars
    rw [thm] at a8
    simp at a8
    let ⟨qoweiur, asrrrrf⟩ := a8
    rw [asrrrrf]
    simp [thm]
    have : (BitVec.toNat i + 1) % 256 = (i + 1).toNat := by
      simp
    rw [this]
    rw [BitVec.ofNat_toNat]
    simp
    change x + i + 1#8 = x + (i + 1#8)
    bv_decide
  · rename_i hh
    change b = 0 at hh
    bv_decide
  · rename_i t tt
    change b = 0 at tt
    congr
    simp [tt, Nat.repeat]
  · steps
    simp_all
    rw [thm]
    simp_all
