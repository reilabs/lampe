import Lampe.Builtin.Basic

namespace Lampe.Builtin

inductive refOmni : Omni where
| mk {P st tp Q v}:
  (∀ref, ref ∉ st → Q (some (st.insert ref ⟨tp, v⟩, LensRef.mk ref []))) →
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
| mk {P st tp Q} {lensRef : LensRef} {base_tp : Tp} {base_val : Tp.denote P base_tp}
    {v : Tp.denote P tp} :
  st.lookup lensRef.ref = some ⟨base_tp, base_val⟩ →
  Tp.followPath (p := P) base_tp base_val lensRef.path tp = some v →
  Q (some (st, v)) →
  readRefOmni P st [tp.ref] tp h![lensRef] Q

def readRef : Builtin := {
  omni := readRefOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type readRefOmni
    constructor <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type readRefOmni
    constructor
    · rw [Finmap.lookup_union_left]
      assumption
      apply Finmap.mem_of_lookup_eq_some
      assumption
    · assumption
    · repeat apply Exists.intro
      tauto
}

inductive writeRefOmni : Omni where
| mk {P st tp Q} {lensRef : LensRef} {base_tp : Tp} {base_val base_val' : Tp.denote P base_tp}
    {v : Tp.denote P tp} :
  st.lookup lensRef.ref = some ⟨base_tp, base_val⟩ →
  Tp.modifyAtPath (p := P) base_tp base_val lensRef.path tp v = some base_val' →
  Q (some (st.insert lensRef.ref ⟨base_tp, base_val'⟩, ())) →
  writeRefOmni P st [tp.ref, tp] .unit h![lensRef, v] Q

def writeRef : Builtin := {
  omni := writeRefOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type writeRefOmni
    constructor <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type writeRefOmni
    constructor
    · rw [Finmap.lookup_union_left]
      assumption
      apply Finmap.mem_of_lookup_eq_some
      assumption
    · assumption
    · repeat apply Exists.intro
      apply And.intro ?_
      simp_all [Finmap.insert_union]
      apply And.intro rfl
      simp_all
      intro x
      simp
      rintro (_ | _)
      · subst_vars
        apply_assumption
        apply Finmap.mem_of_lookup_eq_some
        assumption
      · apply_assumption
        assumption
}

/-- Project a reference to a sub-field, extending its lens path with a field access. -/
inductive projectRefOmni (idx : Nat) : Omni where
| mk {P st tp₁ tp₂ Q} {lensRef : LensRef} :
  Q (some (st, LensRef.mk lensRef.ref (lensRef.path ++ [.field idx]))) →
  (projectRefOmni idx) P st [Tp.ref tp₁] (Tp.ref tp₂) h![lensRef] Q

def projectRef (idx : Nat) : Builtin := {
  omni := projectRefOmni idx
  conseq := by
    unfold omni_conseq
    intros
    cases_type projectRefOmni
    constructor; tauto
  frame := by
    unfold omni_frame
    intros
    cases_type projectRefOmni
    constructor
    repeat apply Exists.intro
    tauto
}

def zeroed := newGenericTotalPureBuiltin
  (fun (a : Tp) => ⟨[], a⟩)
  (fun {p} a _ => Tp.zero p a)

end Lampe.Builtin
