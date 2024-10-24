import Lampe.State
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.SeparationLogic
import Mathlib

namespace Lampe

abbrev Builtin.Omni := ∀(P:Prime),
    State P →
    (argTps : List Tp) →
    (outTp : Tp) →
    HList (Tp.denote P) argTps →
    (Option (State P × Tp.denote P outTp) → Prop) →
    Prop

def Builtin.omni_conseq (omni : Builtin.Omni) : Prop :=
  ∀{P st argTps outTp args Q Q'}, omni P st argTps outTp args Q → (∀ r, Q r → Q' r) → omni P st argTps outTp args Q'

def Builtin.omni_frame (omni : Builtin.Omni) : Prop :=
  ∀{P st₁ st₂ argTps outTp args Q}, omni P st₁ argTps outTp args Q → st₁.Disjoint st₂ →
    omni P (st₁ ∪ st₂) argTps outTp args (fun r => match r with
      | some (st, v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st
      | none => Q none
    )

structure Builtin where
  omni : Builtin.Omni
  conseq : Builtin.omni_conseq omni
  frame : Builtin.omni_frame omni

namespace Builtin

inductive assertOmni : Omni where
| t {st Q} : Q (some (st, ())) → assertOmni P st [.bool] .unit h![true] Q
| f {st Q} : Q none → assertOmni P st [.bool] .unit h![false] Q

def assert : Builtin := {
  omni := assertOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type assertOmni <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type assertOmni
    · constructor
      repeat apply Exists.intro
      tauto
    · constructor; tauto
}

inductive eqOmni : Omni
| f {P st a b Q} : Q (some (st, a == b)) → eqOmni P st [.field, .field] .bool h![a, b] Q
| u {P st s a b Q} : Q (some (st, a == b)) → eqOmni P st [.u s, .u s] .bool h![a, b] Q

def eq : Builtin := {
  omni := eqOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type eqOmni <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type eqOmni <;> {
      constructor
      repeat apply Exists.intro
      tauto
    }
}

inductive freshOmni : Omni where
| mk {P st tp Q} : (∀ v, Q (some (st, v))) → freshOmni P st [] tp h![] Q

def fresh : Builtin := {
  omni := freshOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type freshOmni
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type freshOmni
    constructor
    intro
    repeat apply Exists.intro
    tauto
}

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
    simp_all [Finmap.insert_eq_singleton_union, Finmap.disjoint_union_left]
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

inductive addUOmni : Omni where
| mk {P st s a b Q} :
    (noOverflowHp: a.val + b.val < 2^s → Q (some (st, a + b))) →
    (overFlow: a.val + b.val ≥ 2^s → Q none) →
    addUOmni P st [.u s, .u s] (.u s) h![a, b] Q

-- [TODO: Utknan – pick one representation]
inductive addUOmni' : Omni where
| noOverflow {P st s a b Q} :
    a.val + b.val < 2^s → Q (some (st, a + b)) → addUOmni' P st [.u s, .u s] (.u s) h![a, b] Q
| overflow {P st s a b Q} :
    a.val + b.val ≥ 2^s → Q none → addUOmni' P st [.u s, .u s] (.u s) h![a, b] Q

theorem both_defs_are_the_same : addUOmni = addUOmni' := by
  funext
  simp only [eq_iff_iff]
  apply Iff.intro
  · intro hp
    cases hp with
    | @mk P st s a b Q _ _ =>
      cases Nat.lt_or_ge (a.val + b.val) (2^s) with
      | inl h =>
        apply addUOmni'.noOverflow <;> tauto
      | inr h =>
        apply addUOmni'.overflow <;> tauto
  · rintro (_ | _) <;> (constructor <;> (first | tauto | intro; linarith))

def addU : Builtin := {
  omni := addUOmni
  conseq := by
    unfold omni_conseq
    sorry
  frame := by sorry

}

end Lampe.Builtin
