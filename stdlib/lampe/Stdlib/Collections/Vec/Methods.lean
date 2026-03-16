import Stdlib.Collections.Vec.Core

namespace Lampe.Stdlib.Collections.Vec

open «std-1.0.0-beta.14»

set_option linter.deprecated false

/-!
`collections::vec`

Hoare-logic specs for `Vec` methods.
Each spec is stated in terms of `embed` and standard Lean `List` operations.
-/

private theorem consequence_post
    {P : SLP (State p)} {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_hoare : STHoare p Γ P e Q₁) (h : ∀ v, Q₁ v ⊢ Q₂ v) :
    STHoare p Γ P e Q₂ :=
  STHoare.consequence SLP.entails_self (fun v => SLP.star_mono_r (h v)) h_hoare

private theorem SLP.singleton_entails_exists_star_lift
    {ref : Ref} {tp : Tp}
    {v : Tp.denote p tp}
    {P : Tp.denote p tp → Prop}
    (h : P v) :
    ([ref ↦ ⟨tp, v⟩] : SLP (State p))
      ⊢ (∃∃ v', [ref ↦ ⟨tp, v'⟩] ⋆ ⟦P v'⟧) := by
  intro st hst
  exact ⟨v, st, ∅, by simp, by simp, hst, h, rfl⟩

theorem new_spec {p T} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::vec::Vec::new».call h![T] h![])
      (fun r => embed r = []) := by
  enter_decl; steps; subst_vars; rfl

theorem from_vector_spec {p T s} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::vec::Vec::from_vector».call h![T] h![s])
      (fun r => embed r = s) := by
  enter_decl; steps; subst_vars; rfl

theorem len_spec {p T self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::vec::Vec::len».call h![T] h![self])
      (fun r => r.toNat = (embed self).length) := by
  enter_decl; steps; subst_vars; simp [embed, slice]

theorem get_spec {p T self index}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::vec::Vec::get».call h![T] h![self, index])
      (fun r => r = (embed self)[index.toNat]'hindex) := by
  enter_decl; steps; subst_vars; simp_all [embed, slice]

private theorem set_concrete_spec {p T selfRef self index value}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::set».call h![T] h![selfRef, index, value])
      (fun _ =>
        [selfRef ↦ ⟨vecTp T,
          Builtin.replaceTuple' self Builtin.Member.head
            (Builtin.replaceSlice' (slice self) ⟨index.toNat, hindex⟩ value)⟩]) := by
  enter_decl; steps; all_goals simp_all [slice, embed, vecTp]

theorem set_spec {p T selfRef self index value}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::set».call h![T] h![selfRef, index, value])
      (fun _ => V selfRef ((embed self).set index.toNat value)) := by
  unfold V
  have hsl : index.toNat < (Builtin.indexTpl self Builtin.Member.head).length := hindex
  exact consequence_post (set_concrete_spec (hindex := hindex))
    fun _ => SLP.singleton_entails_exists_star_lift (by
      simp [embed, slice, Builtin.replaceSlice', Builtin.index_replaced_tpl,
        List.modify_eq_set_getElem?, List.getElem?_eq_getElem hsl])

private theorem push_concrete_spec {p T selfRef self elem} :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::push».call h![T] h![selfRef, elem])
      (fun _ =>
        [selfRef ↦ ⟨vecTp T,
          Builtin.replaceTuple' self Builtin.Member.head (slice self ++ [elem])⟩]) := by
  enter_decl; steps

theorem push_spec {p T selfRef self elem} :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::push».call h![T] h![selfRef, elem])
      (fun _ => V selfRef (embed self ++ [elem])) := by
  unfold V
  exact consequence_post push_concrete_spec
    fun _ => SLP.singleton_entails_exists_star_lift (by simp [embed, slice])

private theorem pop_concrete_spec {p T selfRef self}
    (hnonempty : embed self ≠ []) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::pop».call h![T] h![selfRef])
      (fun r =>
        [selfRef ↦ ⟨vecTp T,
          Builtin.replaceTuple' self Builtin.Member.head (embed self).dropLast⟩] ⋆
          ⟦r = (embed self).getLast hnonempty⟧) := by
  enter_decl; steps
  simp only [slice, embed] at hnonempty
  steps [STHoare.pureBuiltin_intro
    (a := T) (sgn := fun tp => ⟨[.slice tp], .tuple none [.slice tp, tp]⟩)
    (desc := fun _ h![l] => ⟨l ≠ [], fun h => (l.dropLast, l.getLast h, ())⟩)]
  all_goals simp_all [slice, embed, Builtin.indexTpl]

theorem pop_spec {p T selfRef self}
    (hnonempty : embed self ≠ []) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::pop».call h![T] h![selfRef])
      (fun r =>
        V selfRef ((embed self).dropLast) ⋆
          ⟦r = (embed self).getLast hnonempty⟧) := by
  unfold V embed
  apply consequence_post (pop_concrete_spec (by exact hnonempty))
  intro r st ⟨st₁, st₂, hdis, hunion, hsingleton, hpure, hempty⟩
  exact ⟨st₁, st₂, hdis, hunion, ⟨_, st₁, ∅, by simp, by simp, hsingleton, rfl, rfl⟩, hpure, hempty⟩

private theorem insert_concrete_spec {p T selfRef self index elem}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::insert».call h![T] h![selfRef, index, elem])
      (fun _ =>
        [selfRef ↦ ⟨vecTp T,
          Builtin.replaceTuple' self Builtin.Member.head
            ((embed self).insertIdx index.toNat elem)⟩]) := by
  enter_decl; steps
  simp only [slice, embed] at hindex
  steps [STHoare.pureBuiltin_intro
    (a := T) (sgn := fun tp => ⟨[.slice tp, .u 32, tp], .slice tp⟩)
    (desc := fun _ h![l, i, e] => ⟨i.toNat < l.length, fun _ => l.insertIdx i.toNat e⟩)]

-- Note: the underlying sliceInsert builtin requires strict `<`; the Noir stdlib
-- accepts `≤` (inserting at the end) but the Lampe model currently does not.
theorem insert_spec {p T selfRef self index elem}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::insert».call h![T] h![selfRef, index, elem])
      (fun _ => V selfRef ((embed self).insertIdx index.toNat elem)) := by
  unfold V
  exact consequence_post (insert_concrete_spec hindex)
    fun _ => SLP.singleton_entails_exists_star_lift (by simp [embed, slice])

private theorem remove_concrete_spec {p T selfRef self index}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::remove».call h![T] h![selfRef, index])
      (fun r =>
        [selfRef ↦ ⟨vecTp T,
          Builtin.replaceTuple' self Builtin.Member.head
            ((embed self).eraseIdx index.toNat)⟩] ⋆
          ⟦r = (embed self).get ⟨index.toNat, hindex⟩⟧) := by
  enter_decl; steps
  simp only [slice, embed] at hindex
  steps [STHoare.pureBuiltin_intro
    (a := T) (sgn := fun tp => ⟨[.slice tp, .u 32], .tuple none [.slice tp, tp]⟩)
    (desc := fun _ h![l, i] => ⟨i.toNat < l.length, fun h => (l.eraseIdx i.toNat, l.get (Fin.mk i.toNat h), ())⟩)]
  all_goals simp_all [slice, embed, Builtin.indexTpl]

theorem remove_spec {p T selfRef self index}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::remove».call h![T] h![selfRef, index])
      (fun r =>
        V selfRef ((embed self).eraseIdx index.toNat) ⋆
          ⟦r = (embed self)[index.toNat]'hindex⟧) := by
  unfold V embed
  apply consequence_post (remove_concrete_spec (by exact hindex))
  intro r st ⟨st₁, st₂, hdis, hunion, hsingleton, hpure, hempty⟩
  refine ⟨st₁, st₂, hdis, hunion, ⟨_, st₁, ∅, by simp, by simp, hsingleton, rfl, rfl⟩, ?_, hempty⟩
  simp [List.get_eq_getElem] at hpure; exact hpure

end Lampe.Stdlib.Collections.Vec
