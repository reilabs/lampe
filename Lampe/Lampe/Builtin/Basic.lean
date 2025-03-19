import Lampe.SeparationLogic.ValHeap
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.Builtin.Helpers
import Mathlib.Tactic.Lemma

lemma List.replicate_head (hl : x :: xs = List.replicate n a) : x = a := by
  unfold List.replicate at hl
  aesop

lemma List.replicate_cons (hl : x :: xs = List.replicate n a) : xs = List.replicate (n-1) a := by
  unfold List.replicate at hl
  cases xs <;> aesop

@[reducible]
def HList.toList (l : HList rep tps) (_ : tps = List.replicate n tp) : List (rep tp) := match l with
| .nil => []
| .cons x xs => match tps with
  | [] => []
  | _ :: _ => ((List.replicate_head (by tauto)) ▸ x) :: (HList.toList xs (List.replicate_cons (by tauto)))

@[reducible, simp]
def HList.head (l : HList rep (tp :: tps)) : rep tp := match l with
| .cons x _ => x

@[reducible, simp]
def HList.tail (l : HList rep (tp :: tps)) : HList rep tps := match l with
| .cons _ xs => xs

namespace Lampe

lemma HList.toList_cons {head}:
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
def HList.toVec (l : HList rep tps) (h_same : tps = List.replicate n tp) : List.Vector (rep tp) n :=
  ⟨HList.toList l h_same, by apply HList.toList_length_is_n⟩

@[reducible]
def HList.toTuple (hList : HList (Tp.denote p) tps) (name : Option String) : Tp.denote p $ .tuple name tps  := match hList with
| .nil => ()
| .cons arg args => ⟨arg, HList.toTuple args name⟩

abbrev Builtin.Omni (argTps : List Tp) (outTp : Tp) := ∀(P:Prime),
    ValHeap P →
    HList (Tp.denote P) argTps →
    (Option (ValHeap P × Tp.denote P outTp) → Prop) →
    Prop

def Builtin.omni_conseq {argTps outTp} (omni : Builtin.Omni argTps outTp) : Prop :=
  ∀ {P st args Q Q'},
  omni P st args Q → (∀ r, Q r → Q' r) → omni P st args Q'

def Builtin.omni_frame {argTps outTp} (omni : Builtin.Omni argTps outTp) : Prop :=
  ∀ {P st₁ st₂ args Q},
  omni P st₁ args Q →
  st₁.Disjoint st₂ →
  omni P (st₁ ∪ st₂) args (fun r => match r with
    | some (st, v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st
    | none => Q none
  )

def ExecuteWithHints (argTps : List Tp) (outTp : Tp) : Type := ∀(P:Prime),
    List (AnyValue P) →
    ValHeap P →
    HList (Tp.denote P) argTps →
    Option (List (AnyValue P) × Option (ValHeap P × Tp.denote P outTp))

def execution_reachable {argTps outTp} (omni : Builtin.Omni argTps outTp) (exe : ExecuteWithHints argTps outTp) : Prop :=
  ∀ {P hints st args}, match exe P hints st args with
    | some (_, st') => ¬omni P st args (fun r => r ≠ st')
    | none => True

structure Builtin (argTps : List Tp) (outTp : Tp) where
  omni : Builtin.Omni argTps outTp
  conseq : Builtin.omni_conseq omni
  frame : Builtin.omni_frame omni
  exe : ExecuteWithHints argTps outTp
  reachable : execution_reachable omni exe

end Lampe

namespace Lampe.Builtin

inductive genericPureOmni
  (argTps : List Tp)
  (outTp : Tp)
  (pred : {p : Prime} → HList (Tp.denote p) argTps → Prop)
  (decidablePred : {p : Prime} → (as : HList (Tp.denote p) argTps) → Decidable (pred as))
  (desc : {p : Prime} → (args : HList (Tp.denote p) argTps) → pred args → Tp.denote p outTp)
   : Omni argTps outTp where
  | ok {p st args Q}:
    (h : pred args)
      → Q (some (st, desc args h))
      → (genericPureOmni argTps outTp pred decidablePred desc) p st args Q
  | err {p st args Q}:
    ¬(pred args)
      → Q none
      → (genericPureOmni argTps outTp pred decidablePred desc) p st args Q

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
def newGenericPureBuiltin
  (argTps : List Tp)
  (outTp : Tp)
  (pred : {p : Prime} → HList (Tp.denote p) argTps → Prop)
  [decidablePred: ∀{p}, ∀(as : HList (Tp.denote p) argTps), Decidable (pred as)]
  (desc : {p : Prime} → (args : HList (Tp.denote p) argTps) → pred args → Tp.denote p outTp) : Builtin argTps outTp := {
  omni := genericPureOmni argTps outTp pred decidablePred desc
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
  exe := fun P hints st args => some $ match decidablePred args with
    | isTrue h => (hints, st, desc args h)
    | isFalse _ => (hints, none)

  reachable := by
    unfold execution_reachable
    intro _ _ _ args
    intro h
    cases h
    · rename_i hpred hok
      have : decidablePred args = isTrue hpred := by
        cases decidablePred args <;> tauto
      simp_all
    · rename_i hpred herr
      have : decidablePred args = isFalse hpred := by
        cases decidablePred args <;> tauto
      simp_all
}

def newGenericTotalPureBuiltin
  (argTps : List Tp)
  (outTp : Tp)
  (desc : {p : Prime} → HList (Tp.denote p) argTps → Tp.denote p outTp) : Builtin argTps outTp :=
  newGenericPureBuiltin argTps outTp (fun _ => True) (fun args _ => desc args)

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
def newPureBuiltin := newGenericPureBuiltin

def newTotalPureBuiltin := newGenericTotalPureBuiltin

/--
Defines the assertion builtin that takes a boolean. We assume the following:
- If `a == true`, it evaluates to `()`.
- Else, an exception is thrown.
-/
def assert := newPureBuiltin [.bool] .unit (fun h => h.head) (fun _ _ => ())


inductive freshOmni (out : Tp) : Omni [] out where
| mk {P st Q} : (∀ v, Q (some (st, v))) → freshOmni out P st h![] Q

/--
Corresponds to an unconstrained function call
-/
def fresh (out : Tp) : Builtin [] out := {
  omni := freshOmni out
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
  exe := fun P hints st args => match hints with
  | [] => none
  | (⟨tp, v⟩ :: hs) => if h:tp = out then some (hs, some (st, h▸v)) else none
  reachable := by
    simp [execution_reachable]
    intro _ hints _ args
    cases hints
    · simp
    · rename_i h _
      cases h
      simp only
      split
      · intro h
        cases h
        simp_all
      · trivial
}

end Lampe.Builtin
