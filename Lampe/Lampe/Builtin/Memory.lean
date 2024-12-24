import Lampe.Builtin.Basic
import Lampe.Lens

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

inductive readLensOmni (lens : Lens tp₁ tp₂) : Omni where
| mk {p st Q ref} {v : Tp.denote p tp₁} :
  st.lookup ref = some ⟨tp₁, v⟩ → Q (some (st, lens.get v)) →
  (readLensOmni lens) p st [tp₁.ref] tp₂ h![ref] Q

def readLens (lens : Lens tp₁ tp₂) : Builtin := {
  omni := readLensOmni lens
  conseq := by
    unfold omni_conseq
    intros
    cases_type readLensOmni
    constructor
    assumption
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type readLensOmni
    constructor
    rw [Finmap.lookup_union_left]
    assumption
    apply Finmap.mem_of_lookup_eq_some
    assumption
    repeat apply Exists.intro
    tauto
}

inductive readRefOmni : Omni where
| mk {P st tp Q ref} {v : Tp.denote P tp} :
  st.lookup ref = some ⟨tp, v⟩ → Q (some (st, v)) →
  readRefOmni P st [tp.ref] tp h![ref] Q

-- [TODO] deprecate and replace with readLens
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

inductive modifyLensOmni (lens : Lens tp₁ tp₂) : Omni where
| mk {p st Q ref} {v : Tp.denote p tp₁} {v' : Tp.denote p tp₂}  :
  st.lookup ref = some ⟨tp₁, v⟩ →
  Q (some (st.insert ref ⟨tp₁, lens.modify v v'⟩, ())) →
  (modifyLensOmni lens) p st [tp₁.ref, tp₂] .unit h![ref, v'] Q

def modifyLens (lens : Lens tp₁ tp₂) : Builtin := {
  omni := modifyLensOmni lens
  conseq := by
    unfold omni_conseq
    intros
    cases_type modifyLensOmni
    constructor <;> aesop
  frame := by
    unfold omni_frame
    intros
    rename_i p st₁ st₂ hd outTp args Q _ hd
    cases_type modifyLensOmni
    . constructor
      rw [Finmap.lookup_union_left] <;> tauto
      apply Finmap.mem_of_lookup_eq_some <;> tauto
      simp_all
      repeat apply Exists.intro
      apply And.intro ?_
      . simp_all only [Finmap.insert_union]
        apply And.intro rfl (by tauto)
      . apply Finmap.disjoint_insert <;> tauto
}

end Lampe.Builtin
