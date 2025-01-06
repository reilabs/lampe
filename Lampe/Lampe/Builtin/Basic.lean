import Lampe.SeparationLogic.ValHeap
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.Builtin.Helpers
import Mathlib

lemma List.replicate_head (hl : x :: xs = List.replicate n a) : x = a := by
  unfold List.replicate at hl
  aesop

lemma List.replicate_cons (hl : x :: xs = List.replicate n a) : xs = List.replicate (n-1) a := by
  unfold List.replicate at hl
  cases xs <;> aesop

namespace Lampe

@[reducible]
def HList.toList (l : HList rep tps) (_ : tps = List.replicate n tp) : List (rep tp) := match l with
| .nil => []
| .cons x xs => match tps with
  | [] => []
  | _ :: _ => ((List.replicate_head (by tauto)) ▸ x) :: (HList.toList xs (List.replicate_cons (by tauto)))

lemma HList.toList_cons :
    HList.toList (n := n + 1) (HList.cons head rem) h₁ = head :: (HList.toList (n := n) rem h₂) := by
  rfl

lemma HList.toList_length_is_n (h_same : tps = List.replicate n tp) :
  (HList.toList l h_same).length = n := by
  subst h_same
  induction n
  cases l
  tauto
  cases l
  rw [HList.toList_cons]
  simp_all
  rfl

@[reducible]
def HList.toVec (l : HList rep tps) (h_same : tps = List.replicate n tp) : Mathlib.Vector (rep tp) n :=
  ⟨HList.toList l h_same, by apply HList.toList_length_is_n⟩

@[reducible]
def HList.toTuple (hList : HList (Tp.denote p) tps) (name : Option String) : Tp.denote p $ .tuple name tps  := match hList with
| .nil => ()
| .cons arg args => ⟨arg, HList.toTuple args name⟩

abbrev Builtin.Omni := ∀(P:Prime),
    ValHeap P →
    (argTps : List Tp) →
    (outTp : Tp) →
    HList (Tp.denote P) argTps →
    (Option (ValHeap P × Tp.denote P outTp) → Prop) →
    Prop

def Builtin.omni_conseq (omni : Builtin.Omni) : Prop :=
  ∀ {P st argTps outTp args Q Q'},
  omni P st argTps outTp args Q → (∀ r, Q r → Q' r) → omni P st argTps outTp args Q'

def Builtin.omni_frame (omni : Builtin.Omni) : Prop :=
  ∀ {P st₁ st₂ argTps outTp args Q},
  omni P st₁ argTps outTp args Q →
  st₁.Disjoint st₂ →
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
    → (h : Prop) × (h → (Tp.denote p (sgn a).snd))) : Builtin := {
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
    → (h : Prop) × (h → (Tp.denote p sgn.snd))) :=
    newGenericPureBuiltin
      (fun (_ : Unit) => sgn)
      (fun _ args => desc args)

/--
Defines the assertion builtin that takes a boolean. We assume the following:
- If `a == true`, it evaluates to `()`.
- Else, an exception is thrown.
-/
def assert := newPureBuiltin
  ⟨[.bool], .unit⟩
  (fun h![a] => ⟨a == true,
    fun _ => ()⟩)

inductive freshOmni : Omni where
| mk {P st tp Q} : (∀ v, Q (some (st, v))) → freshOmni P st [] tp h![] Q

/--
Corresponds to an unconstrained function call
-/
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

end Lampe.Builtin
