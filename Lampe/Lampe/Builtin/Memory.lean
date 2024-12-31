import Lampe.Builtin.Basic
import Lampe.Lens

lemma Finmap.insert_mem_disjoint [DecidableEq α] {m₁ m₂ : Finmap fun _ : α => β} {hd : m₁.Disjoint m₂} {he : ref ∈ m₁} :
  (m₁.insert ref v).Disjoint m₂ := by
  rw [Finmap.insert_eq_singleton_union]
  have _ : ref ∉ m₂ := by aesop
  simp only [Finmap.disjoint_union_left]
  aesop

namespace Lampe.Builtin

inductive refOmni : Omni where
| mk {P st tp Q v}: (∀ref, ref ∉ st → Q (some (st.insert ref ⟨tp, v⟩, ref))) →
  refOmni P st [tp] (tp.ref) h![v] Q

def ref : Builtin := {
  omni := refOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type refOmni
    constructor
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type refOmni
    constructor
    intros
    repeat apply Exists.intro
    apply And.intro ?_
    apply And.intro ?_
    apply And.intro
    apply_assumption
    simp_all
    rfl
    simp [Finmap.insert_union]
    simp_all [Finmap.insert_eq_singleton_union, LawfulHeap.disjoint, Finmap.disjoint_union_left]
}

inductive readRefOmni : Omni where
| mk {P st tp Q ref} {v : Tp.denote P tp} :
  st.lookup ref = some ⟨tp, v⟩ → Q (some (st, v)) →
  readRefOmni P st [tp.ref] tp h![ref] Q

def readRef : Builtin := {
  omni := readRefOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type readRefOmni
    constructor
    assumption
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type readRefOmni
    constructor
    rw [Finmap.lookup_union_left]
    assumption
    apply Finmap.mem_of_lookup_eq_some
    assumption
    repeat apply Exists.intro
    tauto
}

inductive writeRefOmni : Omni where
| mk {P st tp Q ref} {v : Tp.denote P tp} :
  ref ∈ st →
  Q (some (st.insert ref ⟨tp, v⟩, ())) →
  writeRefOmni P st [tp.ref, tp] .unit h![ref, v] Q

def writeRef : Builtin := {
  omni := writeRefOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type writeRefOmni
    constructor
    tauto
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type writeRefOmni
    constructor
    simp_all
    repeat apply Exists.intro
    apply And.intro ?_
    simp_all [Finmap.insert_union]
    apply And.intro rfl
    simp_all
    intro x
    simp
    rintro (_ | _)
    · subst_vars
      apply_assumption
      assumption
    · apply_assumption
      assumption
}

inductive readLensOmni (lens : Lens rep tp₁ tp₂) : Omni where
 | ok {st Q ref} {s : Tp.denote p tp₁} {hr : rep = Tp.denote p} :
   st.lookup ref = some ⟨tp₁, hr ▸ s⟩ →
   (some v = Lens.get (hr ▸ lens) s) →
   Q (some (st, v)) →
   (readLensOmni lens) p st [tp₁.ref] tp₂ h![ref] Q
| err {st Q ref} {s : Tp.denote p tp₁} {hr : rep = Tp.denote p} :
   st.lookup ref = some ⟨tp₁, hr ▸ s⟩ →
   (none = Lens.get (hr ▸ lens) s) →
   Q none →
   (readLensOmni lens) p st [tp₁.ref] tp₂ h![ref] Q

 def readLens (lens : Lens rep tp₁ tp₂) : Builtin := {
   omni := readLensOmni lens
   conseq := by
    unfold omni_conseq
    intros
    cases_type readLensOmni
    constructor <;> tauto
    apply readLensOmni.err <;> tauto
   frame := by
    unfold omni_frame
    intros
    cases_type readLensOmni
    . constructor <;> tauto
      rw [Finmap.lookup_union_left] <;> tauto
      apply Finmap.mem_of_lookup_eq_some <;> tauto
      repeat apply Exists.intro <;> tauto
    . apply readLensOmni.err <;> tauto
      rw [Finmap.lookup_union_left] <;> tauto
      apply Finmap.mem_of_lookup_eq_some <;> tauto
 }

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

end Lampe.Builtin
