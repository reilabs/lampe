-- This module serves as the root of the `Lampe` library.
-- Import modules here that should be built as part of the library.
import «Lampe».Basic
import Lean.Meta.Tactic.Simp.Main

open Lampe

def weirdEq : Lampe.FunctionDecl := nrfn![ fn weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}]

def assertEq : Lampe.FunctionDecl := .mk "assertEq"
    { generics := [.type]
      inTps := fun h![T] => [T, T]
      outTp := fun _ => .unit
      body := fun _ => fun h![T] => fun h![a, b] =>
        .letIn (.call h![] T (.builtin .fresh) h![]) fun x =>
          .seq
            (.call h![] .unit (.builtin .assert) h![
              .call h![] .bool (.builtin .eq) h![.var x, .var a]
            ])
            (.call h![] .unit (.builtin .assert) h![
              .call h![] .bool (.builtin .eq) h![.var x, .var b]
            ])
    }

#print weirdEq
#print assertEq

def recursiveMul : Lampe.Function := {
  generics := []
  inTps := fun _ => [.u 64, .u 64]
  outTp := fun _ => .u 64
  body := fun _ => fun h![] => fun h![n, k] =>
    .ite
      (.call h![] .bool (.builtin .eq) h![.var n, .lit (.u 64) 0])
      (.lit (.u 64) 0)
      (.letIn (.call h![] (.u 64) (.builtin .sub) h![.var n, .lit (.u 64) 1]) fun n =>
        .call h![] (.u 64) (.builtin .add) h![
          .var k,
          .call h![] (.u 64) (.decl "recursiveMul") h![.var n, .var k]
        ]
      )
}

def testMod : Lampe.Module := ⟨[assertEq, ⟨"recursiveMul", recursiveMul⟩]⟩

section macros
open Lean Elab.Tactic Parser.Tactic Lean.Meta

def discharge (prop : Expr) : SimpM (Option Expr) := do
    try
      let mvar ← mkFreshExprMVar prop
      withTransparency TransparencyMode.all mvar.mvarId!.refl
      return some mvar
    catch _ => pure ()

    Simp.dischargeDefault? prop

elab "noir_simp_discharge" : tactic => wrapSimpDischarger discharge

syntax "noir_simp" (config)? (discharger)? (&" only")? (simpArgs)? (location)? : tactic

elab_rules : tactic
| `(tactic|noir_simp $[$cfg:config]? $[(discharger := $dis)]? $[only%$only?]?
    $[$sa:simpArgs]? $[$loc:location]?) => withMainContext do
  let _ ← elabSimpConfig (mkOptionalNode cfg) .simp
end macros

open Lampe

syntax "nr_simp_wip" : tactic
macro_rules
|`(tactic|nr_simp_wip) => `(tactic|
  simp (disch := (first | noir_simp_discharge | decide)) only [
    -- true_and,
    -- and_true,
    -- Assignable.of_BigStep,
    -- Assignable.blockNext_iff,
    Assignable.callBuiltin_iff,
    Assignable.callDecl_iff,
    Assignable.ite_iff,
    Assignable.letIn_iff,
    Assignable.lit_u_iff,
    Assignable.lit_true_iff,
    Assignable.lit_false_iff,
    Assignable.proj_iff,
    Assignable.seq_iff,
    Assignable.struct_iff,
    Assignable.var_iff,



    Assignable.Args.nil_iff,
    Assignable.Args.cons_iff,
    -- Assignable.callArgPrepNext_iff,
    -- Assignable.callArgsPrepDoneBuiltin_iff,
    -- Assignable.blockDone_iff,
    -- List.nil_append,
    -- List.cons_append,
    -- List.indexOf_cons_ne,
    -- List.indexOf_cons_eq,
    -- List.get!_cons_succ,
    -- List.get!_cons_zero,
    -- decide_eq_true_iff,
    -- Assignable.Builtin.assert_iff,
    Assignable.Builtin.add_u_iff,
    Assignable.Builtin.assert_iff,
    Assignable.Builtin.eq_f_iff,
    Assignable.Builtin.eq_u_iff,
    Assignable.Builtin.fresh_iff,
    Assignable.Builtin.sub_u_iff,

    -- Mathlib.Vector.get_mk_cons,
    -- Mathlib.Vector.get_mk_zero,
    Assignable.Ite.iff_true,
    Assignable.Ite.iff_false,
    -- Assignable.lit_field_iff,

    Assignable.Fields.nil_iff,
    Assignable.Fields.cons_iff,
  ]
)

theorem assignable_assertEq_field_iff:
  Assignable Γ st (assertEq.fn.body _ h![.field] h![a, b]) Q ↔
  a = b ∧ Q st () := by
  simp only [assertEq]
  nr_simp_wip
  simp

theorem assignable_weirdEq_field_iff:
  Assignable Γ st (weirdEq.fn.body _ h![.field] h![a, b]) Q ↔
  a = b ∧ Q st () := by
  simp only [weirdEq]
  nr_simp_wip
  simp

theorem Fin.castSucc_val : Fin.val (Fin.castSucc a) = a := by
  rfl

theorem Fin.succ_val : Fin.val (Fin.succ a) = a.val + 1 := by
  rfl

theorem assignableRecursiveMul [Fact (Nat.Prime P)]:
    Assignable (P := P) (Lampe.Env.ofModule testMod) st (recursiveMul.body _ h![] h![a, b]) Q ↔
    (a.val * b.val < 2 ^ 64) ∧ Q st (a * b) := by
  induction a using Fin.induction generalizing Q with
  | zero =>
      simp only [recursiveMul]
      nr_simp_wip
      simp
  | succ a ih =>
      simp only [recursiveMul]
      nr_simp_wip
      have : a.succ - Nat.cast 1 = a.castSucc := by
        cases a
        conv => lhs; whnf
        conv => rhs; whnf
        simp_arith
        linarith
      simp only [this, ih, Fin.mul_def, Fin.add_def, Fin.castSucc_val, Fin.succ_val]
      simp_arith [Nat.add_mul, Nat.add_comm]
      apply Iff.intro
      · intro_cases
        apply And.intro <;> try assumption
        rename _ + _ * _ % _ ≤ _ => h
        rw [Nat.mod_eq_of_lt] at h <;> linarith
      · intro_cases
        apply And.intro (by linarith)
        apply And.intro
        · rw [Nat.mod_eq_of_lt] <;> linarith
        · assumption

example :
    ∃st' sc', BigStep 17 (stdlib.extend (Lampe.Env.ofModule testMod)) st sc (.callArgPrep (.decl "lt_fallback") [⟨.field, 10⟩, ⟨.field, 5⟩] []) st' sc' ⟨.bool, true⟩ := by
  simp (disch := with_unfolding_all rfl) only [BigStep.callArgPrepDeclDone_iff3]
  unfold BigStepCall
  crush
  simp [Field.numBits, Nat.log2]
  conv in (occs := *) (Fin.val _ / Fin.val _) => whnf
  simp [BigStep.loopCont_iff]
  crush
  apply And.intro
  · decide
  · apply Exists.intro
    use [10]
    crush
    apply And.intro (by decide)
    use [22]
    crush
    apply And.intro (by decide)
    apply And.intro rfl
    simp [State.alloc, State.set]


@[reducible]
def «std::Option» : Struct :=
{
  name := "std::Option"
  tyArgKinds := [.type]
  fieldTypes := fun h![T] => [.bool, T]
}

def «std::Option::some» : Lampe.FunctionDecl := .mk "std::Option::some"
  {
    generics := [.type]
    inTps := fun h![T] => [T]
    outTp := fun h![T] => «std::Option».tp h![T]
    body := fun _ => fun h![T] => fun h![x] =>
      «std::Option».constructor h![T] h![.lit .bool 1, .var x]
  }

def «std::Option::unwrap» : Lampe.FunctionDecl := .mk "std::Option::unwrap"
  {
    generics := [.type]
    inTps := fun h![T] => [«std::Option».tp h![T]]
    outTp := fun h![T] => T
    body := fun _ h![_] h![opt] =>
      (Expr.call h![] .unit (.builtin .assert) h![
        .proj .head (.var opt)
      ]).seq (.proj Member.head.tail (.var opt))
  }

@[reducible]
def mod := Env.ofModule ⟨[«std::Option::some», «std::Option::unwrap»]⟩

theorem unwrap_some {st : State P} {T e Q} :
  Assignable mod st (
    .call h![T] T (.decl "std::Option::unwrap") h![
      .call h![T] («std::Option».tp h![T]) (.decl "std::Option::some") h![e]
    ]
  ) Q ↔ Assignable mod st e Q := by
  nr_simp_wip
  simp only [«std::Option::unwrap», «std::Option::some»]
  nr_simp_wip
  simp


def «std::U128» : Struct :=
{
  name := "std::U128"
  tyArgKinds := []
  fieldTypes := fun _ => [.field, .field]
}

def «std::U128::from_u64s_le» : FunctionDecl := .mk "std::U128::from_u64s_le"
{
  generics := []
  inTps := fun _ => [.u 64, .u 64]
  outTp := fun _ => «std::U128».tp h![]
  body := fun _ => fun h![] h![lo, hi] =>
    .seq
      (.call h![] .unit (.builtin .assert) h![
        .call h![] .bool (.builtin .)
      ])
      («std::U128».constructor h![] h![
        .call h![] .field (.builtin .cast) h![.var lo],
        .call h![] .field (.builtin .cast) h![.var hi]
      ])
}


theorem test {n : Nat}: ∃foo, n = foo := by apply Exists.intro n rfl

theorem test2 : 1 + 2 = n := by
  rcases test with ⟨_, h⟩
  simp only [h]
