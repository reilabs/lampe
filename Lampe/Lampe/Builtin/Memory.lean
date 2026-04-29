import Lampe.Builtin.Basic

namespace Lampe.Builtin

inductive refOmni : Omni where
| mk {P st tp Q v}:
  (∀ref, ref ∉ st → Q (some (st.insert ref ⟨tp, v⟩, LensRef.mk tp ref .nil))) →
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
| mk {P st tp Q} {lensRef : LensRef tp} {base_val : Tp.denote P lensRef.base_tp} :
  st.lookup lensRef.ref = some ⟨lensRef.base_tp, base_val⟩ →
  Q (some (st, RuntimeLens.get P lensRef.lens base_val)) →
  readRefOmni P st [Tp.ref tp] tp h![lensRef] Q

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
    · repeat apply Exists.intro
      tauto
}

inductive writeRefOmni : Omni where
| mk {P st tp Q} {lensRef : LensRef tp} {base_val : Tp.denote P lensRef.base_tp}
    {v : Tp.denote P tp} :
  st.lookup lensRef.ref = some ⟨lensRef.base_tp, base_val⟩ →
  Q (some (st.insert lensRef.ref ⟨lensRef.base_tp, RuntimeLens.modify P lensRef.lens base_val v⟩, ())) →
  writeRefOmni P st [Tp.ref tp, tp] .unit h![lensRef, v] Q

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

/-- Project a reference by appending a path segment (like GEP). Pure — no heap interaction. -/
def projectRef (acc : RuntimeAccess tp₁ tp₂) : Builtin :=
  newTotalPureBuiltin
    ⟨[Tp.ref tp₁], Tp.ref tp₂⟩
    (fun h![lensRef] => LensRef.mk lensRef.base_tp lensRef.ref (lensRef.lens.append acc))

def zeroed := newGenericTotalPureBuiltin
  (fun (a : Tp) => ⟨[], a⟩)
  (fun {p} a _ => Tp.zero p a)

end Lampe.Builtin
