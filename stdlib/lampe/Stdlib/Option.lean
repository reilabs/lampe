import «std-1.0.0-beta.12».Extracted
import Stdlib.Cmp
import Lampe

namespace Lampe.Stdlib.Option

open «std-1.0.0-beta.12»
open Cmp.Ord

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

/--
Convert a Lean option into a Noir `std-1.0.0-beta.12::option::Option`.

We recommend providing the user with `std-1.0.0-beta.12::option::Option`s at the boundary of the theorem for any
option values 'created' by the theorem.
-/
def fromOption {p t} : Option (t.denote p) -> («std-1.0.0-beta.12::option::Option».tp h![t] |>.denote p)
| none => (false, Tp.zero p t, ())
| some val => (true, val, ())

/--
Convert a Noir `std-1.0.0-beta.12::option::Option` into a Lean option.

We recommend converting user-provided `std-1.0.0-beta.12::option::Option`s from the user, and converting them
within the theorem.
-/
def toOption {p t} : («std-1.0.0-beta.12::option::Option».tp h![t] |>.denote p) -> Option (t.denote p)
| (false, _, _) => none
| (true, val, _) => some val

@[simp]
lemma fromOption_toOption_id : toOption (fromOption v) = v := by
  cases v <;> rfl

@[simp]
lemma option_fst_eq_toOption_isSome {p T}
    {v : Tp.denote p $ «std-1.0.0-beta.12::option::Option».tp h![T]}
  : Builtin.indexTpl v Builtin.Member.head = (toOption v).isSome := by
  rcases v with ⟨_|_, _⟩
  all_goals rfl

@[simp]
lemma option_snd_eq_toOption_get_of_isSome {p T}
    {v : Tp.denote p $ «std-1.0.0-beta.12::option::Option».tp h![T]}
    (v_is_some : (toOption v).isSome = true)
  : Builtin.indexTpl v Builtin.Member.head.tail = (toOption v).get v_is_some := by
  rcases v with ⟨_|_, _, _⟩
  · contradiction
  · rfl

lemma getD_map_of_isSome {α β} {f : α → β} {d : β} {o : Option α}
    (h : o.isSome)
  : (o.map f).getD d = f (o.get h) := by
  rcases (Option.isSome_iff_exists.mp h) with ⟨_, rfl⟩
  rfl

@[simp]
lemma bind_def_of_isSome {α β} {v : Option α} {f : α → Option β} (v_is_some : v.isSome = true)
  : v >>= f = f (v.get v_is_some) := by
  rcases (Option.isSome_iff_exists.mp v_is_some) with ⟨_, rfl⟩
  simp_all

theorem none_spec {p T} : STHoare p env ⟦⟧ («std-1.0.0-beta.12::option::Option::none».call h![T] h![])
    (fun v => v = fromOption none) := by
  enter_decl
  steps
  subst_vars
  rfl

theorem some_spec {p T v} : STHoare p env ⟦⟧ («std-1.0.0-beta.12::option::Option::some».call h![T] h![v])
    (fun r => r = fromOption (some v)) := by
  enter_decl
  steps
  subst_vars
  rfl

theorem is_none_spec {p T v} : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::is_none».call h![T] h![v])
    (fun r => r = (toOption v).isNone) := by
  enter_decl
  steps
  subst_vars
  simp

theorem is_some_spec {p T v} : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::is_some».call h![T] h![v])
    (fun r => r = (toOption v).isSome) := by
  enter_decl
  steps
  subst_vars
  simp

theorem unwrap_spec {p T v} : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::unwrap».call h![T] h![v])
    (fun r => ∃h, r = (toOption v).get h) := by
  enter_decl
  steps
  simp only [option_fst_eq_toOption_isSome, beq_true] at *
  rename _ = true => v
  use v
  subst_vars
  rename Tp.denote p («std-1.0.0-beta.12::option::Option».tp _) => h
  rcases h with ⟨(_|_), _, _⟩
  · contradiction
  · rfl

theorem map_none_spec {p T U E f v}
    (v_is_none : (toOption v).isNone)
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::map».call h![T, U, E] h![v, f])
    (fun r => r = fromOption none) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  · simp_all

  steps [none_spec]
  simp_all

theorem map_some_spec {p T U E f fb v P Q}
    (v_is_some : (toOption v).isSome)
    (h_lam : STHoare p env P (fb h![(toOption v).get v_is_some]) Q)
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::option::Option::map».call h![T, U, E] h![v, f])
    (fun r => (∃∃vin, r = fromOption (some vin) ⋆ Q vin) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  · simp_all

  steps
  simp only [option_snd_eq_toOption_get_of_isSome v_is_some]
  steps [STHoare.callLambda_intro (hlam := h_lam), some_spec]
  case _ : _ = _ => assumption
  sl

theorem map_pure_spec {p T U E P f fb v}
    {f_emb : T.denote p → U.denote p}
    (h_f : ∀arg, STHoare p env P (fb h![arg]) (fun r => r = f_emb arg ⋆ P))
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::option::Option::map».call h![T, U, E] h![v, f])
    (fun r => r = fromOption ((toOption v).map f_emb) ⋆ P) := by
  by_cases h : (toOption v).isSome = true
  · steps [map_some_spec h (h_f _)]
    subst_vars
    simp only [←Option.map_some, Option.some_get]
  · steps [map_none_spec]
    all_goals simp_all

theorem map_or_none_spec {p T U E v default f}
    (v_is_none : (toOption v).isNone)
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::map_or».call h![T, U, E] h![v, default, f])
    (fun r => r = default) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  · simp_all

  steps
  simp_all

theorem map_or_some_spec {p T U E v f fb default P Q}
    (v_is_some : (toOption v).isSome)
    (h_lam : STHoare p env P (fb h![(toOption v).get v_is_some]) Q)
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::option::Option::map_or».call h![T, U, E] h![v, default, f])
    (fun r => Q r ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  · simp_all

  steps
  simp only [option_snd_eq_toOption_get_of_isSome v_is_some]
  steps [STHoare.callLambda_intro (hlam := h_lam), some_spec]

theorem map_or_pure_spec {p T U E P v f fb default}
    {f_emb : T.denote p → U.denote p}
    (h_f : ∀arg, STHoare p env P (fb h![arg]) (fun r => r = f_emb arg ⋆ P))
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::option::Option::map_or».call h![T, U, E] h![v, default, f])
    (fun r => r = ((toOption v).map f_emb).getD default ⋆ P) := by
  by_cases h : (toOption v).isSome = true
  · steps [map_or_some_spec (E := E) h (h_f _)]
    subst_vars
    rw [getD_map_of_isSome (f := f_emb) h]
  · steps [map_or_none_spec]
    all_goals simp_all

theorem map_or_else_none_spec {p T U E1 E2 P Q v default default_b func}
    (v_is_none : (toOption v).isNone)
    (default_f : STHoare p env P (default_b h![]) Q)
  : STHoare p env
    (P ⋆ [λdefault ↦ default_b])
    («std-1.0.0-beta.12::option::Option::map_or_else».call h![T, U, E1, E2] h![v, default, func])
    (fun r => Q r ⋆ [λdefault ↦ default_b]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  · simp_all

  steps [STHoare.callLambda_intro (hlam := default_f)]

theorem map_or_else_some_spec {p T U E1 E2 P Q v default func func_b}
    (v_is_some : (toOption v).isSome)
    (func_f : STHoare p env P (func_b h![(toOption v).get v_is_some]) Q)
  : STHoare p env
    (P ⋆ [λfunc ↦ func_b])
    («std-1.0.0-beta.12::option::Option::map_or_else».call h![T, U, E1, E2] h![v, default, func])
    (fun r => Q r ⋆ [λfunc ↦ func_b]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  · simp_all

  steps
  simp only [option_snd_eq_toOption_get_of_isSome v_is_some]
  steps [STHoare.callLambda_intro (hlam := func_f)]

theorem map_or_else_pure_spec {p T U E1 E2 P v default default_b func func_b}
    {default_emb : U.denote p}
    {func_emb : T.denote p → U.denote p}
    (default_f : STHoare p env P (default_b h![]) (fun r => r = default_emb ⋆ P))
    (func_f : ∀arg, STHoare p env P (func_b h![arg]) (fun r => r = func_emb arg ⋆ P))
  : STHoare p env
    (P ⋆ [λdefault ↦ default_b] ⋆ [λfunc ↦ func_b])
    («std-1.0.0-beta.12::option::Option::map_or_else».call h![T, U, E1, E2] h![v, default, func])
    (fun r => r = ((toOption v).map func_emb).getD default_emb ⋆ P) := by
  by_cases h : (toOption v).isSome = true
  · steps [map_or_else_some_spec (E1 := E1) (E2 := E2) h (func_f _)]
    subst_vars
    rw [getD_map_of_isSome (f := func_emb) h]
  · have h : (toOption v).isNone := by
      simp_all
    steps [map_or_else_none_spec (E1 := E1) (E2 := E2) h default_f]
    subst_vars
    simp_all

theorem and_spec {p T v w}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::and».call h![T] h![v, w])
    (fun r => r = if (toOption v).isSome then w else fromOption none) := by
  enter_decl
  steps [is_none_spec]
  apply STHoare.ite_intro
  · intro cond
    steps [none_spec]
    simp_all
  · intro cond
    steps
    simp_all

theorem and_then_none_spec {p T U E self f}
    (self_is_none : (toOption self).isNone)
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::and_then».call h![T, U, E] h![self, f])
    (fun r => r = fromOption none) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  · simp_all

  steps [none_spec]
  simp_all

theorem and_then_some_spec {p T U E P Q self f fb}
    (self_is_some : (toOption self).isSome)
    (f_lam : STHoare p env P (fb h![(toOption self).get self_is_some]) Q)
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::option::Option::and_then».call h![T, U, E] h![self, f])
    (fun r => Q r ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  · simp_all

  steps
  simp [option_snd_eq_toOption_get_of_isSome self_is_some]
  steps [STHoare.callLambda_intro (hlam := f_lam)]

theorem and_then_pure_spec {p T U E P self f fb}
    {f_emb : T.denote p → (Tp.denote p $ «std-1.0.0-beta.12::option::Option».tp h![U])}
    (f_f : ∀arg, STHoare p env P (fb h![arg]) (fun r => r = f_emb arg ⋆ P))
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::option::Option::and_then».call h![T, U, E] h![self, f])
    (fun r => r = ((toOption self).map f_emb).getD (fromOption none) ⋆ P) := by
  by_cases h : (toOption self).isSome = true
  · steps [and_then_some_spec (E := E) h (f_f _)]
    subst_vars
    rw [getD_map_of_isSome h]
  · have h : (toOption self).isNone := by simp_all
    steps [and_then_none_spec (E := E) h]
    simp_all

theorem or_spec {p T self default}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::or».call h![T] h![self, default])
    (fun r => r = if (toOption self).isSome then self else default) := by
  enter_decl
  steps
  apply STHoare.ite_intro
  · intro cond
    rw [option_fst_eq_toOption_isSome] at cond
    steps
    subst_vars
    simp_all
  · intro cond
    rw [option_fst_eq_toOption_isSome] at cond
    simp_all only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, Option.isSome_none,
                   Bool.false_eq_true, ↓reduceIte]
    steps
    simp_all

theorem or_else_none_spec {p T E P Q self default default_b}
    (self_is_none : (toOption self).isNone)
    (default_f : STHoare p env P (default_b h![]) Q)
  : STHoare p env
    (P ⋆ [λdefault ↦ default_b])
    («std-1.0.0-beta.12::option::Option::or_else».call h![T, E] h![self, default])
    (fun r => Q r ⋆ [λdefault ↦ default_b]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  · simp_all

  steps [STHoare.callLambda_intro (hlam := default_f)]

theorem or_else_some_spec {p T E self default}
    (self_is_some : (toOption self).isSome)
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::or_else».call h![T, E] h![self, default])
    (fun r => r = self) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  · simp_all

  steps
  simp_all

theorem or_else_pure_spec {p T E P self default default_b}
    {default_emb : Tp.denote p $ «std-1.0.0-beta.12::option::Option».tp h![T]}
    (default_f : STHoare p env P (default_b h![]) (fun r => r = default_emb ⋆ P))
  : STHoare p env
    (P ⋆ [λdefault ↦ default_b])
    («std-1.0.0-beta.12::option::Option::or_else».call h![T, E] h![self, default])
    (fun r => (r = if (toOption self).isSome then self else default_emb) ⋆ P) := by
  by_cases h : (toOption self).isSome = true
  . steps [or_else_some_spec h]
    subst_vars
    simp_all
  · have h : (toOption self).isNone := by simp_all
    steps [or_else_none_spec (E := E) h default_f]
    subst_vars
    simp_all

theorem xor_spec {p T self other}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::xor».call h![T] h![self, other])
    (fun r => r = if (toOption self).isSome then
        if (toOption other).isSome then fromOption none else self
      else if (toOption other).isSome then
        other
      else
        fromOption none
    ) := by
  enter_decl
  steps
  apply STHoare.ite_intro
  · intros
    steps
    apply STHoare.ite_intro
    · intros
      steps [none_spec]
      simp_all
    · intros
      steps
      simp_all
  · intros
    steps
    apply STHoare.ite_intro
    · intros
      steps
      simp_all
    · intros
      steps [none_spec]
      simp_all

theorem filter_none_spec {p T E self pred}
    (self_is_none : (toOption self).isNone)
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::filter».call h![T, E] h![self, pred])
    (fun r => r = fromOption none) := by
  enter_decl
  steps
  rw [option_fst_eq_toOption_isSome]
  apply STHoare.ite_intro_of_false
  · simp_all

  steps [none_spec]
  simp_all

theorem filter_some_spec {p T E P Q self pred pred_b}
    (self_is_some : (toOption self).isSome)
    (pred_f : STHoare p env P (pred_b h![(toOption self).get self_is_some]) Q)
  : STHoare p env
    (P ⋆ [λpred ↦ pred_b])
    («std-1.0.0-beta.12::option::Option::filter».call h![T, E] h![self, pred])
    (fun r => ∃∃b, Q b ⋆ r = if b then self else fromOption none) := by
  enter_decl
  steps
  rw [option_fst_eq_toOption_isSome]
  apply STHoare.ite_intro_of_true
  · simp_all

  steps
  simp_all only [option_snd_eq_toOption_get_of_isSome]
  steps [STHoare.callLambda_intro (hlam := pred_f)]

  apply STHoare.ite_intro
  · intros
    steps unsafe
    subst_vars
    simp_all

  · intros
    steps [none_spec]
    subst_vars
    sl unsafe
    simp_all

theorem flatten_spec {p T opt}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::option::Option::flatten».call h![T] h![opt])
    (fun r => r = (toOption opt).getD (fromOption none)) := by
  enter_decl
  steps
  rw [option_fst_eq_toOption_isSome]
  apply STHoare.ite_intro
  · intros
    steps
    subst_vars
    rw [option_snd_eq_toOption_get_of_isSome]
    rotate_left
    simp_all
    apply Option.get_eq_getD

  · intros
    steps [none_spec]
    subst_vars
    simp_all

set_option maxRecDepth 2000 in
theorem default_spec {p T}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::default::Default».default h![] («std-1.0.0-beta.12::option::Option».tp h![T]) h![] h![] h![])
    (fun r => r = fromOption none) := by
  resolve_trait
  steps [none_spec]
  simp_all

set_option maxRecDepth 2000 in
theorem eq_spec {p T self other P Q}
    {t_eq : «std-1.0.0-beta.12::cmp::Eq».hasImpl env h![] T}
    {eq_f : (h_self : (toOption self).isSome)
          → (h_other : (toOption other).isSome)
          → STHoare p env P
            («std-1.0.0-beta.12::cmp::Eq».eq h![] T h![] h![]
              h![(toOption self).get h_self, (toOption other).get h_other])
            Q}
  : STHoare p env P
    («std-1.0.0-beta.12::cmp::Eq».eq h![] («std-1.0.0-beta.12::option::Option».tp h![T]) h![] h![] h![self, other])
    (fun r => if h : (toOption self).isSome ∧ (toOption other).isSome then
        Q r else (r = ((toOption self).isSome == (toOption other).isSome))) := by
  resolve_trait
  steps
  · exact ()
  apply STHoare.ite_intro
  · simp only [option_fst_eq_toOption_isSome, decide_eq_true_eq, dite_eq_ite]
    intro hp
    steps
    apply STHoare.ite_intro
    · simp only [option_fst_eq_toOption_isSome, decide_eq_true_eq, dite_eq_ite]
      intro hs
      rw [hs, Eq.comm] at hp
      steps
      simp only [option_snd_eq_toOption_get_of_isSome, *]
      steps [eq_f hs hp]
    · simp only [option_fst_eq_toOption_isSome, decide_eq_true_eq, dite_eq_ite]
      intro hp
      simp_all
      steps
      assumption
  · simp only [option_fst_eq_toOption_isSome, decide_eq_false_iff_not, dite_eq_ite]
    intro hp
    split
    · rename_i hh
      rcases hh
      simp_all
    · steps
      subst_vars
      rw [Eq.comm, beq_eq_false_iff_ne]
      assumption

theorem eq_pure_spec {p T self other}
    {t_eq : «std-1.0.0-beta.12::cmp::Eq».hasImpl env h![] T}
    {t_eq_emb : T.denote p → T.denote p → Prop}
    (h_eq : ∀a b, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::cmp::Eq».eq h![] T h![] h![] h![a, b])
      (fun r : Bool => r = t_eq_emb a b))
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::cmp::Eq».eq h![] («std-1.0.0-beta.12::option::Option».tp h![T]) h![] h![] h![self, other])
    (fun r : Bool => r = Option.Rel t_eq_emb (toOption self) (toOption other)) := by
  apply STHoare.consequence_frame
  apply eq_spec
  case t_eq => assumption
  case eq_f =>
    intros
    simp only [←option_snd_eq_toOption_get_of_isSome]
    apply h_eq
  case h_ent => sl
  case q_ent =>
    intros
    simp only [SL.dite_lift_lift]
    sl
    rename_i hp
    split at hp
    · casesm _∧_
      rename_i hs ho
      simp only [hp, option_snd_eq_toOption_get_of_isSome, *]
      conv =>
        rhs
        congr
        · skip
        · rw [←Option.some_get hs]
        · rw [←Option.some_get ho]
      simp only [Option.rel_some_some]
    · generalize toOption self = self at *
      generalize toOption other = other at *
      simp_all only [eq_iff_iff, not_and, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none, beq_iff_eq]
      apply Iff.intro
      · intro hp
        have : self.isSome = false := by
          by_contra
          simp_all
        have : self = none := by simp_all
        have : other = none := by simp_all
        simp only [*, Option.rel_none_none]
      · rintro (_ | _) <;> simp_all

set_option maxRecDepth 2000 in
theorem hash_spec {p T H self P Q R}
    {state : Tp.denote p $ Tp.ref H}
    {t_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] T}
    {t_hash_f : (h_self : (toOption self).isSome) → STHoare p env Q
      («std-1.0.0-beta.12::hash::Hash».hash h![] T h![] h![H] h![(toOption self).get h_self, state]) fun _ => R}
    {bool_hash : «std-1.0.0-beta.12::hash::Hash».hasImpl env h![] Tp.bool}
    {bool_hash_f : STHoare p env P
      («std-1.0.0-beta.12::hash::Hash».hash h![] Tp.bool h![] h![H] h![(toOption self).isSome, state]) fun _ => Q}
  : STHoare p env P
    («std-1.0.0-beta.12::hash::Hash».hash h![] («std-1.0.0-beta.12::option::Option».tp h![T]) h![] h![H] h![self, state])
    (fun _ => if (toOption self).isSome then R else Q) := by
  resolve_trait
  steps

  step_as (P) (fun _ => Q)
  · rw [option_fst_eq_toOption_isSome]
    steps [bool_hash_f]
  · steps
    apply STHoare.ite_intro
    · simp_all only [option_fst_eq_toOption_isSome]
      intros
      steps
      rw [option_snd_eq_toOption_get_of_isSome]
      rename_i a
      steps [t_hash_f a]

    · simp only [option_fst_eq_toOption_isSome, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none]
      intro
      simp_all only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, ↓reduceIte]
      steps

set_option maxRecDepth 2000 in
theorem cmp_spec {p T self other P Q}
    {t_ord : «std-1.0.0-beta.12::cmp::Ord».hasImpl env h![] T}
    (t_ord_f : (h_self : (toOption self).isSome)
             → (h_other : (toOption other).isSome)
             → STHoare p env P
               («std-1.0.0-beta.12::cmp::Ord».cmp h![] T h![] h![]
                h![(toOption self).get h_self, (toOption other).get h_other])
               Q)
  : STHoare p env P
    («std-1.0.0-beta.12::cmp::Ord».cmp h![] («std-1.0.0-beta.12::option::Option».tp h![T]) h![] h![] h![self, other])
    (fun r => if (toOption self).isSome then
      if (toOption other).isSome then Q r else r = fromOrdering .gt
    else if (toOption other).isSome then r = fromOrdering .lt else
      r = fromOrdering .eq) := by
  resolve_trait
  steps
  rw [option_fst_eq_toOption_isSome]
  apply STHoare.ite_intro
  · intro s_some
    steps
    rw [option_fst_eq_toOption_isSome]
    apply STHoare.ite_intro
    · intro o_some
      steps
      rw [option_snd_eq_toOption_get_of_isSome o_some, option_snd_eq_toOption_get_of_isSome s_some]
      steps [t_ord_f s_some o_some]
      simp_all only [forall_true_left, ↓reduceIte]
      sl
    · intro o_none
      steps
      conv => rhs; simp [s_some, o_none]
      steps [greater_spec]
      simp_all
  · intro s_none
    steps
    rw [option_fst_eq_toOption_isSome]
    apply STHoare.ite_intro
    · intro o_some
      steps
      conv => rhs; simp [s_none, o_some]
      steps [less_spec]
      simp_all
    · intro o_none
      steps
      conv => rhs; simp [s_none, o_none]
      steps [equal_spec]
      simp_all

set_option maxRecDepth 2000 in
theorem cmp_pure_spec {p T self other}
    {t_ord : «std-1.0.0-beta.12::cmp::Ord».hasImpl env h![] T}
    {t_ord_emb : T.denote p → T.denote p → («std-1.0.0-beta.12::cmp::Ordering».tp h![] |>.denote p)}
    (t_ord_f : ∀a b, STHoare p env ⟦⟧
      («std-1.0.0-beta.12::cmp::Ord».cmp h![] T h![] h![] h![a, b])
      (fun r => r = t_ord_emb a b))
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::cmp::Ord».cmp h![] («std-1.0.0-beta.12::option::Option».tp h![T]) h![] h![] h![self, other])
    (fun r => r = if h : (toOption self).isSome then
      if g : (toOption other).isSome then
        t_ord_emb ((toOption self).get h) ((toOption other).get g)
      else fromOrdering .gt
    else if (toOption other).isSome then fromOrdering .lt else
      fromOrdering .eq) := by
  resolve_trait
  steps
  rw [option_fst_eq_toOption_isSome]
  apply STHoare.ite_intro
  · intro s_some
    steps
    rw [option_fst_eq_toOption_isSome]
    apply STHoare.ite_intro
    · intro o_some
      steps
      rw [option_snd_eq_toOption_get_of_isSome o_some, option_snd_eq_toOption_get_of_isSome s_some]
      steps [t_ord_f ((toOption self).get s_some) ((toOption other).get o_some)]
      simp_all
    · intro
      steps [greater_spec]
      simp_all

  · intro s_none
    steps
    rw [option_fst_eq_toOption_isSome]
    apply STHoare.ite_intro
    · intro
      steps [less_spec]
      simp_all
    · intro
      steps [equal_spec]
      simp_all

