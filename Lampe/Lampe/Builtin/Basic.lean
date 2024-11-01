import Lampe.State
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.SeparationLogic
import Lampe.Builtin.Helpers
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

end Lampe

namespace Lampe.Builtin

inductive pureBuiltinOmni
  (argTps : List Tp)
  (outTp : Tp)
  (pred : {p : Prime} → (HList (Tp.denote p) argTps) → Prop)
  (comp : {p : Prime} → (args: HList (Tp.denote p) argTps) → (pred args) → (Tp.denote p outTp)) : Omni where
  | ok {p st args Q}:
    (h : pred args)
      → Q (some (st, comp args h))
      → (pureBuiltinOmni argTps outTp pred comp) p st argTps outTp args Q
  | err {p st args Q}:
    ¬(pred args)
      → Q none
      → (pureBuiltinOmni argTps outTp pred comp) p st argTps outTp args Q

/--
A pure deterministic `Builtin` definition.
Takes a list of input types `argTps : List Tp`, an output type `outTp : Tp`, a predicate `pred` and evaluation function `comp`.
For `args: HList (Tp.denote p) argTps`, we assume that a builtin function *fails* when `¬(pred args)`, and it *succeeds* when `pred args`.

If the builtin succeeds, it evaluates to `some (comp args (h : pred))`.
Otherwise, it evaluates to `none`.
-/
def newPureBuiltin
  (argTps : List Tp)
  (outTp : Tp)
  (pred : {p : Prime} → (HList (Tp.denote p) argTps) → Prop)
  (comp : {p : Prime} → (args: HList (Tp.denote p) argTps) → (pred args) → (Tp.denote p outTp)) : Builtin := {
  omni := (pureBuiltinOmni argTps outTp pred comp)
  conseq := by
    unfold omni_conseq
    intros
    cases_type pureBuiltinOmni
    . constructor <;> simp_all
    . apply pureBuiltinOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type pureBuiltinOmni
    . constructor
      . constructor <;> tauto
    . apply pureBuiltinOmni.err <;> assumption
}

/--
Defines the assertion builtin that takes a boolean. We assume the following:
- If `a == true`, it evaluates to `()`.
- Else, an exception is thrown.
-/
def assert : Builtin := newPureBuiltin
  [.bool] .unit
  (fun h![a] => a == true)
  (fun _ _ => ())

end Lampe.Builtin
