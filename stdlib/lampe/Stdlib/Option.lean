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

set_option maxRecDepth 1000

def from_option {p t}: Option (t.denote p) -> («std::option::Option».tp h![t] |>.denote p)
| none => (false, Tp.zero p t, ())
| some val => (true, val, ())

theorem none_spec {p T} : STHoare p env ⟦⟧ («std::option::Option::none».call h![T] h![]) 
    (fun v => v = from_option none) := by
  enter_decl
  steps
  assumption

theorem some_spec {p T v} : STHoare p env ⟦⟧ («std::option::Option::some».call h![T] h![v])
    (fun r => r = from_option (some v)) := by
  enter_decl
  steps
  assumption

theorem is_none_spec {p T v} : STHoare p env ⟦⟧ 
    («std::option::Option::is_none».call h![T] h![from_option v]) 
    (fun r => r = v.isNone) := by
  enter_decl
  steps
  subst_vars
  cases v <;> rfl
  exact ()

theorem is_some_spec {p T v} : STHoare p env ⟦⟧ 
    («std::option::Option::is_some».call h![T] h![from_option v]) 
    (fun r => r = v.isSome) := by
  enter_decl
  steps
  subst_vars
  cases v <;> rfl

theorem unwrap_spec {p T v} : STHoare p env ⟦⟧ 
    («std::option::Option::unwrap».call h![T] h![from_option v]) 
    (fun r => ∃h, r = v.get h) := by
  enter_decl
  steps
  cases v
  · subst_vars
    rename _ = _ => hp
    cases hp
  · subst_vars
    simp
    rfl

theorem map_none_spec {p T U E f} : STHoare p env ⟦⟧ 
    («std::option::Option::map».call h![T, U, E] h![from_option none, f]) 
    (fun r => r = from_option (none: Option (U.denote p))) := by
  enter_decl
  steps
  apply STHoare.iteFalse_intro
  steps [none_spec]
  assumption

theorem map_some_spec {p T U E f fb v P Q}
    (h_lam : STHoare p env P (fb h![v]) Q)
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std::option::Option::map».call h![T, U, E] h![from_option (some v), f])
    (fun v => (∃∃vin, v = (from_option (some vin)) ⋆ Q vin) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply STHoare.iteTrue_intro
  steps [STHoare.callLambda_intro (hlam := h_lam), some_spec]
  case _ : _ = _ => assumption
  sl

theorem map_pure_spec {p T U E f fb v f_emb}
    (h_f : ∀arg, STHoare p env ⟦⟧ (fb h![arg]) (fun r => r = f_emb arg))
  : STHoare p env 
    [λf ↦ fb] 
    («std::option::Option::map».call h![T, U, E] h![from_option v, f]) 
    (fun r => r = from_option (v.map f_emb)) := by
  cases v
  · steps [map_none_spec]
    assumption
  · steps [map_some_spec (h_f _)]
    simp_all

theorem map_or_none_spec {p T U E f default} 
  : STHoare p env ⟦⟧
    («std::option::Option::map_or».call h![T, U, E] h![from_option none, default, f])
    (fun r => r = default) := by
  enter_decl
  steps
  apply STHoare.iteFalse_intro
  steps
  assumption

theorem map_or_some_spec {p T U E f v fb P Q default} 
    (h_lam : STHoare p env P (fb h![v]) Q)
  : STHoare p env
    (P ⋆ [λf ↦ fb])
    («std::option::Option::map_or».call h![T, U, E] h![from_option (some v), default, f])
    (fun v => Q v ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply STHoare.iteTrue_intro
  steps [STHoare.callLambda_intro (hlam := h_lam)]

lemma map_or_pure_spec {p T U E f fb v} 
    {default : U.denote p}
    {f_emb : T.denote p → U.denote p}
    (h_f : ∀arg, STHoare p env ⟦⟧ (fb h![arg]) (fun r => r = f_emb arg))
  : STHoare p env
    [λf ↦ fb]
    («std::option::Option::map_or».call h![T, U, E] h![from_option v, default, f])
    (fun r => r = (v.map f_emb).getD default) := by
  cases v
  . steps [map_or_none_spec]
    assumption
  . steps [map_or_some_spec (E := E) (h_f _)]
    simp_all
    

