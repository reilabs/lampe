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
| none => (false, Lampe.Tp.zero p t, ())
| some val => (true, val, ())

def to_option {p t}: («std::option::Option».tp h![t] |>.denote p) -> Option (t.denote p)
| (false, _, _) => none
| (true, val, _) => some val

lemma from_option_to_option_id : to_option (from_option v) = v := by
  cases v <;> rfl

lemma none_spec {p T} : Lampe.STHoare p env ⟦⟧ («std::option::Option::none».call h![T] h![]) 
    (fun v => v = from_option none) := by
  enter_decl
  steps
  assumption

lemma some_spec {p T v} : Lampe.STHoare p env ⟦⟧ («std::option::Option::some».call h![T] h![v])
    (fun r => r = from_option (some v)) := by
  enter_decl
  steps
  assumption

lemma is_none_spec {p T v} : Lampe.STHoare p env ⟦⟧ 
    («std::option::Option::is_none».call h![T] h![from_option v]) 
    (fun r => r = v.isNone) := by
  enter_decl
  steps
  subst_vars
  cases v <;> rfl
  exact ()

lemma is_some_spec {p T v} : Lampe.STHoare p env ⟦⟧ 
    («std::option::Option::is_some».call h![T] h![from_option v]) 
    (fun r => r = v.isSome) := by
  enter_decl
  steps
  subst_vars
  cases v <;> rfl

lemma unwrap_spec {p T v} : Lampe.STHoare p env ⟦⟧ 
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

lemma map_none_spec {p T U E f} : Lampe.STHoare p env ⟦⟧ 
  («std::option::Option::map».call h![T, U, E] h![from_option none, f]) 
  (fun r => r = from_option (none: Option (U.denote p))) := by
  enter_decl
  steps
  apply Lampe.STHoare.iteFalse_intro
  steps [none_spec]
  assumption

lemma map_some_spec {p T U E f fb v P Q}
    (h_lam : Lampe.STHoare p env P (fb h![v]) Q):
    Lampe.STHoare p env
      (P ⋆ [λf ↦ fb])
      («std::option::Option::map».call h![T, U, E] h![from_option (some v), f])
      (fun v => (∃∃vin, v = (from_option (some vin)) ⋆ Q vin) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  apply Lampe.STHoare.iteTrue_intro
  steps [Lampe.STHoare.callLambda_intro (hlam := h_lam), some_spec]
  case _ : _ = _ => assumption
  sl

lemma map_pure_spec {p T U E f fb v f_emb}
    (h_f: ∀arg, Lampe.STHoare p env ⟦⟧ (fb h![arg]) (fun r => r = f_emb arg)):
    Lampe.STHoare p env 
      [λf ↦ fb] 
      («std::option::Option::map».call h![T, U, E] h![from_option v, f]) 
      (fun r => r = from_option (v.map f_emb)) := by
  cases v
  · steps [map_none_spec]
    assumption
  · steps [map_some_spec (h_f _)]
    simp_all
