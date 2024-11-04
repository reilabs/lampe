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
  (sgn : List Tp × Tp)
  (desc : {p : Prime}
    → (args : HList (Tp.denote p) sgn.fst)
    → (h : Prop) × (h → (Tp.denote p sgn.snd)))
  : Omni where
  | ok {p st args Q}:
    (h : (desc args).fst)
      → Q (some (st, (desc args).snd h))
      → (pureBuiltinOmni sgn desc) p st sgn.fst sgn.snd args Q
  | err {p st args Q}:
    ¬((desc args).fst)
      → Q none
      → (pureBuiltinOmni sgn desc) p st sgn.fst sgn.snd args Q

/--
A pure deterministic `Builtin` definition.
Takes a signature `sgn : List Tp × Tp`,
where the first element is a list of input types and the second element is the output type.
Takes a description `desc`,
which is a function that takes arguments `args : HList (Tp.denote p) sgn.fst`
and returns a predicate `h : Prop` and an evaluation function `h → (Tp.denote p sgn.snd)`.

If the builtin succeeds, i.e., the predicate `h` succeeds, it evaluates to `some (eval h)` where `eval = (desc args).snd`.
Otherwise, it evaluates to `none`.
-/
def newPureBuiltin
  (sgn : List Tp × Tp)
  (desc : {p : Prime}
    → (args : HList (Tp.denote p) sgn.fst)
    → (h : Prop) × (h → (Tp.denote p sgn.snd)))
   : Builtin := {
  omni := (pureBuiltinOmni sgn desc)
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

inductive genericPureOmni {A : Type}
  (sgn : A → List Tp × Tp)
  (desc : {p : Prime}
    → (a : A)
    → (args : HList (Tp.denote p) (sgn a).fst)
    → (h : Prop) × (h → (Tp.denote p (sgn a).snd)))
   : Omni where
  | ok {p st a args Q}:
    (h : (desc a args).fst)
      → Q (some (st, (desc a args).snd h))
      → (genericPureOmni sgn desc) p st (sgn a).fst (sgn a).snd args Q
  | err {p st a args Q}:
    ¬((desc a args).fst)
      → Q none
      → (genericPureOmni sgn desc) p st (sgn a).fst (sgn a).snd args Q

/--
A generic pure deterministic `Builtin` definition.
Takes a signature `sgn : A → List Tp × Tp`,
where the first element evaluates to a list of input types and the second element evaluates to the output type.
Takes a description `desc`,
which is a function that takes the type evaluation input `a : A` and arguments `args : HList (Tp.denote p) sgn.fst`
and returns a predicate `h : Prop` and an evaluation function `h → (Tp.denote p sgn.snd)`.

If the builtin succeeds, i.e., the predicate `h` succeeds, it evaluates to `some (eval h)` where `eval = (desc a args).snd`.
Otherwise, it evaluates to `none`.
-/
def newGenericPureBuiltin {A : Type}
  (sgn : A → List Tp × Tp)
  (desc : {p : Prime}
    → (a : A)
    → (args : HList (Tp.denote p) (sgn a).fst)
    → (h : Prop) × (h → (Tp.denote p (sgn a).snd)))
: Builtin := {
  omni := genericPureOmni sgn desc
  conseq := by
    unfold omni_conseq
    intros
    cases_type genericPureOmni
    . constructor <;> simp_all
    . apply genericPureOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type genericPureOmni
    . constructor
      . constructor <;> tauto
    . apply genericPureOmni.err <;> assumption
}

/--
Defines the assertion builtin that takes a boolean. We assume the following:
- If `a == true`, it evaluates to `()`.
- Else, an exception is thrown.
-/
def assert : Builtin := newPureBuiltin
  ⟨[.bool], .unit⟩
  (fun h![a] => ⟨a == true,
    fun _ => ()⟩)

end Lampe.Builtin
