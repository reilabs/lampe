import «std-1.0.0-beta.11».Extracted.Option
import «std-1.0.0-beta.11».Extracted.«std-1.0.0-beta.11»
import Lampe

namespace Lampe
namespace Stdlib

export «std-1.0.0-beta.11».Extracted (
  «std::option::Option»
  «std::option::Option::none»
  «std::option::Option::some»
  «std::option::Option::is_none»
  «std::option::Option::is_some»
  «std::option::Option::unwrap»
  «std::option::Option::unwrap_unchecked»
  «std::option::Option::unwrap_or»
  «std::option::Option::unwrap_or_else»
  «std::option::Option::expect»
  «std::option::Option::map»
  «std::option::Option::map_or»
  «std::option::Option::map_or_else»
  «std::option::Option::and»
  «std::option::Option::and_then»
  «std::option::Option::or»
  «std::option::Option::or_else»
  «std::option::Option::xor»
  «std::option::Option::flatten»
  Option.env
)

open «std-1.0.0-beta.11».Extracted

namespace Option

/-- 
Convert a Lean option into a Noir `std::option::Option`.

We recommend providing the user with `std::option::Option`s at the boundary of the theorem for any
option values 'created' by the theorem.
-/
def fromOption {p t} : Option (t.denote p) -> («std::option::Option».tp h![t] |>.denote p)
| none => (false, Tp.zero p t, ())
| some val => (true, val, ())

/-- 
Convert a Noir `std::option::Option` into a Lean option.

We recommend converting user-provided `std::option::Option`s from the user, and converting them
within the theorem.
-/
def toOption {p t} : («std::option::Option».tp h![t] |>.denote p) -> Option (t.denote p)
| (false, _, _) => none
| (true, val, _) => some val

@[simp]
lemma fromOption_toOption_id : toOption (fromOption v) = v := by
  cases v <;> rfl

@[simp]
lemma option_fst_eq_toOption_isSome {p T} 
    {v : Tp.denote p $ «std::option::Option».tp h![T]}
  : Builtin.indexTpl v Builtin.Member.head = (toOption v).isSome := by
  rcases v with ⟨_|_, _⟩ 
  all_goals rfl

@[simp]
lemma option_snd_eq_toOption_get_of_isSome {p T}
    {v : Tp.denote p $ «std::option::Option».tp h![T]}
    (v_is_some : (toOption v).isSome = true)
  : Builtin.indexTpl v Builtin.Member.head.tail = (toOption v).get v_is_some := by
  rcases v with ⟨_|_, _, _⟩ 
  . contradiction
  . rfl

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

theorem none_spec {p T} : STHoare p env ⟦⟧ («std::option::Option::none».call h![T] h![]) 
    (fun v => v = fromOption none) := by
  enter_decl
  steps
  subst_vars
  rfl

theorem some_spec {p T v} : STHoare p env ⟦⟧ («std::option::Option::some».call h![T] h![v])
    (fun r => r = fromOption (some v)) := by
  enter_decl
  steps
  subst_vars
  rfl

theorem is_none_spec {p T v} : STHoare p env ⟦⟧ 
    («std::option::Option::is_none».call h![T] h![v]) 
    (fun r => r = (toOption v).isNone) := by
  enter_decl
  steps
  subst_vars
  simp
  exact ()

theorem is_some_spec {p T v} : STHoare p env ⟦⟧ 
    («std::option::Option::is_some».call h![T] h![v]) 
    (fun r => r = (toOption v).isSome) := by
  enter_decl
  steps
  subst_vars
  simp

theorem unwrap_spec {p T v} : STHoare p env ⟦⟧ 
    («std::option::Option::unwrap».call h![T] h![v]) 
    (fun r => ∃h, r = (toOption v).get h) := by
  enter_decl
  steps
  simp only [option_fst_eq_toOption_isSome, beq_true] at *
  rename _ = true => v
  use v
  subst_vars
  rename Tp.denote p («std::option::Option».tp _) => h
  rcases h with ⟨(_|_), _, _⟩
  . contradiction
  . rfl

theorem map_none_spec {p T U E f v} 
    (v_is_none : (toOption v).isNone)
  : STHoare p env ⟦⟧ 
    («std::option::Option::map».call h![T, U, E] h![v, f]) 
    (fun r => r = fromOption none) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  . simp_all

  steps [none_spec]
  simp_all

theorem map_some_spec {p T U E f fb v P Q}
    (v_is_some : (toOption v).isSome)
    (h_lam : STHoare p env P (fb h![(toOption v).get v_is_some]) Q)
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std::option::Option::map».call h![T, U, E] h![v, f])
    (fun r => (∃∃vin, r = fromOption (some vin) ⋆ Q vin) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  . simp_all

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
    («std::option::Option::map».call h![T, U, E] h![v, f]) 
    (fun r => r = fromOption ((toOption v).map f_emb) ⋆ P) := by
  by_cases h : (toOption v).isSome = true
  . steps [map_some_spec h (h_f _)]
    subst_vars
    simp only [←Option.map_some, Option.some_get]
  . steps [map_none_spec]
    all_goals simp_all

theorem map_or_none_spec {p T U E v default f}
    (v_is_none : (toOption v).isNone)
  : STHoare p env ⟦⟧
    («std::option::Option::map_or».call h![T, U, E] h![v, default, f])
    (fun r => r = default) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  . simp_all
  
  steps
  simp_all

theorem map_or_some_spec {p T U E v f fb default P Q}
    (v_is_some : (toOption v).isSome)
    (h_lam : STHoare p env P (fb h![(toOption v).get v_is_some]) Q)
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std::option::Option::map_or».call h![T, U, E] h![v, default, f])
    (fun r => Q r ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  . simp_all

  steps
  simp only [option_snd_eq_toOption_get_of_isSome v_is_some]
  steps [STHoare.callLambda_intro (hlam := h_lam), some_spec]

theorem map_or_pure_spec {p T U E P v f fb default}
    {f_emb : T.denote p → U.denote p}
    (h_f : ∀arg, STHoare p env P (fb h![arg]) (fun r => r = f_emb arg ⋆ P))
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std::option::Option::map_or».call h![T, U, E] h![v, default, f])
    (fun r => r = ((toOption v).map f_emb).getD default ⋆ P) := by
  by_cases h : (toOption v).isSome = true
  . steps [map_or_some_spec (E := E) h (h_f _)]
    subst_vars
    rw [getD_map_of_isSome (f := f_emb) h]
  . steps [map_or_none_spec]
    all_goals simp_all

theorem map_or_else_none_spec {p T U E1 E2 P Q v default default_b func}
    (v_is_none : (toOption v).isNone)
    (default_f : STHoare p env P (default_b h![]) Q)
  : STHoare p env
    (P ⋆ [λdefault ↦ default_b])
    («std::option::Option::map_or_else».call h![T, U, E1, E2] h![v, default, func])
    (fun r => Q r ⋆ [λdefault ↦ default_b]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  . simp_all

  steps [STHoare.callLambda_intro (hlam := default_f)]

theorem map_or_else_some_spec {p T U E1 E2 P Q v default func func_b}
    (v_is_some : (toOption v).isSome)
    (func_f : STHoare p env P (func_b h![(toOption v).get v_is_some]) Q)
  : STHoare p env
    (P ⋆ [λfunc ↦ func_b])
    («std::option::Option::map_or_else».call h![T, U, E1, E2] h![v, default, func])
    (fun r => Q r ⋆ [λfunc ↦ func_b]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  . simp_all

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
    («std::option::Option::map_or_else».call h![T, U, E1, E2] h![v, default, func])
    (fun r => r = ((toOption v).map func_emb).getD default_emb ⋆ P) := by
  by_cases h : (toOption v).isSome = true
  . steps [map_or_else_some_spec (E1 := E1) (E2 := E2) h (func_f _)]
    subst_vars
    rw [getD_map_of_isSome (f := func_emb) h]
  . have h : (toOption v).isNone := by 
      simp_all
    steps [map_or_else_none_spec (E1 := E1) (E2 := E2) h default_f]
    subst_vars
    simp_all

theorem and_spec {p T v w}
  : STHoare p env ⟦⟧
    («std::option::Option::and».call h![T] h![v, w])
    (fun r => r = if (toOption v).isSome then w else fromOption none) := by
  enter_decl
  steps [is_none_spec]
  apply STHoare.ite_intro
  . intro cond
    steps [none_spec]
    simp_all
  . intro cond
    steps
    simp_all

theorem and_then_none_spec {p T U E self f}
    (self_is_none : (toOption self).isNone)
  : STHoare p env ⟦⟧ 
    («std::option::Option::and_then».call h![T, U, E] h![self, f])
    (fun r => r = fromOption none) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  . simp_all
  
  steps [none_spec]
  simp_all

theorem and_then_some_spec {p T U E P Q self f fb}
    (self_is_some : (toOption self).isSome)
    (f_lam : STHoare p env P (fb h![(toOption self).get self_is_some]) Q)
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std::option::Option::and_then».call h![T, U, E] h![self, f])
    (fun r => Q r ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  . simp_all
  
  steps
  simp [option_snd_eq_toOption_get_of_isSome self_is_some]
  steps [STHoare.callLambda_intro (hlam := f_lam)]

theorem and_then_pure_spec {p T U E P self f fb}
    {f_emb : T.denote p → (Tp.denote p $ «std::option::Option».tp h![U])}
    (f_f : ∀arg, STHoare p env P (fb h![arg]) (fun r => r = f_emb arg ⋆ P))
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std::option::Option::and_then».call h![T, U, E] h![self, f])
    (fun r => r = ((toOption self).map f_emb).getD (fromOption none) ⋆ P) := by
  by_cases h : (toOption self).isSome = true
  . steps [and_then_some_spec (E := E) h (f_f _)]
    subst_vars
    rw [getD_map_of_isSome h]
  . have h : (toOption self).isNone := by simp_all
    steps [and_then_none_spec (E := E) h]
    simp_all

theorem or_spec {p T self default}
  : STHoare p env ⟦⟧
    («std::option::Option::or».call h![T] h![self, default])
    (fun r => r = if (toOption self).isSome then self else default) := by
  enter_decl
  steps
  apply STHoare.ite_intro
  . intro cond
    rw [option_fst_eq_toOption_isSome] at cond
    steps
    subst_vars
    simp_all
  . intro cond
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
    («std::option::Option::or_else».call h![T, E] h![self, default])
    (fun r => Q r ⋆ [λdefault ↦ default_b]) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_false
  . simp_all

  steps [STHoare.callLambda_intro (hlam := default_f)]

theorem or_else_some_spec {p T E self default}
    (self_is_some : (toOption self).isSome)
  : STHoare p env ⟦⟧
    («std::option::Option::or_else».call h![T, E] h![self, default])
    (fun r => r = self) := by
  enter_decl
  steps
  apply STHoare.ite_intro_of_true
  . simp_all

  steps
  simp_all

theorem or_else_pure_spec {p T E P self default default_b}
    {default_emb : Tp.denote p $ «std::option::Option».tp h![T]}
    (default_f : STHoare p env P (default_b h![]) (fun r => r = default_emb ⋆ P))
  : STHoare p env
    (P ⋆ [λdefault ↦ default_b])
    («std::option::Option::or_else».call h![T, E] h![self, default])
    (fun r => (r = if (toOption self).isSome then self else default_emb) ⋆ P) := by
  by_cases h : (toOption self).isSome = true
  . steps [or_else_some_spec h]
    subst_vars
    simp_all
  . have h : (toOption self).isNone := by simp_all
    steps [or_else_none_spec (E := E) h default_f]
    subst_vars
    simp_all

theorem xor_spec {p T self other}
  : STHoare p env ⟦⟧
    («std::option::Option::xor».call h![T] h![self, other])
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
  . intros
    steps
    apply STHoare.ite_intro
    . intros
      steps [none_spec]
      simp_all
    . intros
      steps
      simp_all
  . intros
    steps
    apply STHoare.ite_intro
    . intros
      steps
      simp_all
    . intros
      steps [none_spec]
      simp_all

theorem filter_none_spec {p T E self pred}
    (self_is_none : (toOption self).isNone)
  : STHoare p env ⟦⟧ 
    («std::option::Option::filter».call h![T, E] h![self, pred])
    (fun r => r = fromOption none) := by
  enter_decl
  steps
  rw [option_fst_eq_toOption_isSome]
  apply STHoare.ite_intro_of_false
  . simp_all

  steps [none_spec]
  simp_all

theorem filter_some_spec {p T E P Q self pred pred_b}
    (self_is_some : (toOption self).isSome)
    (pred_f : STHoare p env P (pred_b h![(toOption self).get self_is_some]) Q)
  : STHoare p env
    (P ⋆ [λpred ↦ pred_b])
    («std::option::Option::filter».call h![T, E] h![self, pred])
    (fun r => ∃∃b, Q b ⋆ r = if b then self else fromOption none) := by
  enter_decl
  steps
  rw [option_fst_eq_toOption_isSome]
  apply STHoare.ite_intro_of_true
  . simp_all

  steps
  simp_all only [option_snd_eq_toOption_get_of_isSome]
  steps [STHoare.callLambda_intro (hlam := pred_f)]

  apply STHoare.ite_intro
  . intros
    steps unsafe
    subst_vars
    sl unsafe
    simp_all
      
  . intros
    steps [none_spec]
    subst_vars
    sl unsafe
    simp_all

theorem flatten_spec {p T opt}
  : STHoare p env ⟦⟧
    («std::option::Option::flatten».call h![T] h![opt])
    (fun r => r = (toOption opt).getD (fromOption none)) := by
  enter_decl
  steps
  rw [option_fst_eq_toOption_isSome]
  apply STHoare.ite_intro
  . intros
    steps
    subst_vars
    rw [option_snd_eq_toOption_get_of_isSome]
    rotate_left
    simp_all
    apply Option.get_eq_getD

  . intros
    steps [none_spec]
    subst_vars
    simp_all

theorem default_spec {p T} : STHoare p env ⟦⟧ 
    («std::default::Default».default h![] («std::option::Option».tp h![T]) h![] h![] h![])
    (fun r => r = fromOption none) := by
  resolve_trait
  steps [none_spec]
  simp_all
    
