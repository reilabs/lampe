import Lampe.Builtin.Basic
import Lampe.Lens

lemma Finmap.insert_mem_disjoint [DecidableEq α] {m₁ m₂ : Finmap fun _ : α => β} {hd : m₁.Disjoint m₂} {he : ref ∈ m₁} :
  (m₁.insert ref v).Disjoint m₂ := by
  rw [Finmap.insert_eq_singleton_union]
  have _ : ref ∉ m₂ := by aesop
  simp only [Finmap.disjoint_union_left]
  aesop

namespace Lampe.Builtin

 inductive modifyLensOmni (lens : Lens rep tp₁ tp₂) : Omni where
 | ok {p st Q ref} {s s' : Tp.denote p tp₁} {v' : Tp.denote p tp₂} {hr : rep = Tp.denote p} :
   st.lookup ref = some ⟨tp₁, s⟩ →
   some s' = Lens.modify (hr ▸ lens) s v' →
   Q (some (st.insert ref ⟨tp₁, s'⟩, ())) →
   (modifyLensOmni lens) p st [tp₁.ref, tp₂] .unit h![ref, v'] Q
 | err {p st Q ref} {s s' : Tp.denote p tp₁} {v' : Tp.denote p tp₂} {hr : rep = Tp.denote p} :
   st.lookup ref = some ⟨tp₁, s⟩ →
   none = Lens.modify (hr ▸ lens) s v' →
   Q none →
   (modifyLensOmni lens) p st [tp₁.ref, tp₂] .unit h![ref, v'] Q

 def modifyLens (lens : Lens rep tp₁ tp₂) : Builtin := {
   omni := modifyLensOmni lens
   conseq := by
    unfold omni_conseq
    intros
    cases_type modifyLensOmni
    constructor <;> tauto
    apply modifyLensOmni.err <;> tauto
   frame := by
    unfold omni_frame
    intros
    rename_i p st₁ st₂ hd outTp args Q _ hd
    cases_type modifyLensOmni
    . constructor
      rw [Finmap.lookup_union_left] <;> tauto
      apply Finmap.mem_of_lookup_eq_some <;> tauto
      tauto
      simp only
      generalize hst : (Finmap.insert _ _ (st₁ ∪ st₂)) = st' at *
      unfold SLP.star
      simp only [LawfulHeap.disjoint]
      rename Ref => ref
      rename_i s' _ _ _ _ hQ
      exists (Finmap.singleton ref ⟨tp₁, s'⟩ ∪ st₁), st₂
      rw [←hst]
      apply And.intro
      . rw [←Finmap.insert_eq_singleton_union]
        apply Finmap.insert_mem_disjoint <;> tauto
        apply Finmap.mem_of_lookup_eq_some <;> tauto
      . apply And.intro
        . simp [Finmap.union_assoc, Finmap.insert_eq_singleton_union]
        . apply And.intro ?_ (by rfl)
          simp_all [Finmap.insert_union, Finmap.insert_eq_singleton_union]
    . apply modifyLensOmni.err <;> tauto
      rw [Finmap.lookup_union_left] <;> tauto
      apply Finmap.mem_of_lookup_eq_some <;> tauto
 }

inductive getLensOmni (lens : Lens rep tp₁ tp₂) : Omni where
| ok {st Q} {s : Tp.denote p tp₁} {hr : rep = Tp.denote p} :
  (some v = Lens.get (hr ▸ lens) s) →
  Q (some (st, v)) →
  (getLensOmni lens) p st [tp₁] tp₂ h![s] Q
| err {st Q} {s : Tp.denote p tp₁} {hr : rep = Tp.denote p} :
  (none = Lens.get (hr ▸ lens) s) →
  Q none →
  (getLensOmni lens) p st [tp₁] tp₂ h![s] Q

def getLens (lens : Lens rep tp₁ tp₂) : Builtin := {
  omni := getLensOmni lens
  conseq := by
    unfold omni_conseq
    intros
    cases_type getLensOmni
    constructor <;> tauto
    apply getLensOmni.err <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type getLensOmni
    . constructor <;> tauto
      repeat apply Exists.intro <;> tauto
    . apply getLensOmni.err <;> tauto
}

end Lampe.Builtin
