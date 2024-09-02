-- This module serves as the root of the `Lampe` library.
-- Import modules here that should be built as part of the library.
import «Lampe».Basic
import Lean.Meta.Tactic.Simp.Main

abbrev testMod := noir! {
  fn recursiveMul(n,k) {
    if n == (0 : u 64) then (0 : u 64) else {
      let n = n - (1 : u 64);
      k + recursiveMul(n, k)
    }
  }

  fn assertEq(a,b) {
    let x = fresh;
    assert(x == a);
    assert(x == b);
  }

  fn lt_fallback(x, y) {
    let num_bytes = (((field::modulus_num_bits() #as u 32) + (7: u 32)) / (8 : u 32));
    let x_bytes = field::Field::to_le_bytes(x, num_bytes);
    let y_bytes = field::Field::to_le_bytes(y, num_bytes);
    let mut x_is_lt = false;
    let mut done = false;
    for i in (0 : u 32) .. num_bytes {
        if (!done) then {
            let x_byte = x_bytes[((num_bytes - (1 : u 32)) - i)] #as u 8;
            let y_byte = y_bytes[((num_bytes - (1 : u 32)) - i)] #as u 8;
            let bytes_match = (x_byte == y_byte);
            if (!bytes_match) then {
                x_is_lt = (x_byte < y_byte);
                done = true;
            }
        }
    };
    x_is_lt
  }
}

theorem simplify_binder {p : α → Prop} (hp : ∀x, p x → y = x) : (∃x, p x) ↔ p y := by
  apply Iff.intro
  · intro ⟨x, hp'⟩
    rw [hp x hp']
    assumption
  · intro hp'
    apply Exists.intro y
    assumption

theorem simplify_binder_under_ex {p : α → Prop} {q : β → α} (hp : ∀x, p x → ∃y, x = q y) : (∃x, p x) ↔ ∃y, p (q y) := by
  apply Iff.intro
  · intro ⟨x, hp'⟩
    rcases hp x hp' with ⟨_, ⟨_⟩⟩
    apply Exists.intro
    assumption
  · intro ⟨y, hp'⟩
    apply Exists.intro
    assumption

syntax "introB": tactic
macro_rules | `(tactic|introB) => `(tactic | (intros ; try casesm* _ ∧ _, ∃_, _))

syntax "ex_dsch" :tactic
macro_rules | `(tactic|ex_dsch) => `(tactic | (introB; (first | assumption | (symm; assumption))))

syntax "binder_simp" : tactic
macro_rules
| `(tactic | binder_simp) =>
  `(tactic | (first | simp (disch := ex_dsch) only [simplify_binder]))

syntax "ex_dsch2" :tactic
macro_rules
| `(tactic|ex_dsch2) =>
  `(tactic| introB; apply Exists.intro; assumption)

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
  let cfg ← elabSimpConfig (mkOptionalNode cfg) .simp



syntax "crush" : tactic
macro_rules
| `(tactic|crush) => `(tactic|
  repeat (first | simp | simp (disch := ex_dsch) only [simplify_binder] | simp (disch := ex_dsch2) only [simplify_binder_under_ex] | simp (disch := with_unfolding_all rfl) only [Lampe.BigStepAux.callArgPrepDeclDone_iff]))
end macros

open Lampe

def ConvergeWithPostCond (Γ : Env) (st : State P) (sc : Scope P) (e : ExprAux P) (Q : State P → Scope P → Value P → Prop) : Prop :=
  ∃st' sc' v, BigStepAux P Γ st sc e st' sc' v ∧ Q st' sc' v


def ConvergeWithPostCond.of_BigStepAux :
  BigStepAux P Γ st sc e st' sc' v ↔ ConvergeWithPostCond Γ st sc e (λ st'' sc'' v' => st' = st'' ∧ sc' = sc'' ∧ v' = v) := by
  unfold ConvergeWithPostCond
  apply Iff.intro
  · intro h
    repeat apply Exists.intro
    apply And.intro h
    tauto
  · intro_cases
    subst_vars
    assumption

theorem BigStepAux.exists_scope_blockNext_iff :
  (∃sc', BigStepAux P Γ st sc (.expr (.block es fe)) st' sc' v) ↔
  BigStepAux P Γ st sc (.expr (.block es fe)) st' sc v := by
  cases es <;> simp

theorem BigStepAux.blockNext_iff':
    BigStepAux P Γ st sc (.expr (.block (e::es) r)) st' sc' v ↔
    (∃st'' sc'' a, BigStepAux P Γ st sc (.expr e) st'' sc'' a ∧ BigStepAux P Γ st'' sc'' (.expr (.block es r)) st' sc'' v) ∧ sc' = sc := by
  apply Iff.intro
  · simp
    intro_cases
    subst_vars
    apply And.intro <;> try rfl
    repeat apply Exists.intro
    apply And.intro
    · apply Exists.intro
      assumption
    · assumption
  · simp
    intro_cases
    apply And.intro <;> try assumption
    repeat apply Exists.intro
    apply And.intro <;> assumption

theorem ConvergeWithPostCond.blockNext_iff:
    ConvergeWithPostCond Γ st sc (.expr (.block (e::es) r)) Q ↔
    ConvergeWithPostCond Γ st sc (.expr e) (fun st' sc' _ => ConvergeWithPostCond Γ st' sc' (.expr (.block es r)) fun st' sc'' v => sc' = sc'' ∧ Q st' sc v) := by
    simp [ConvergeWithPostCond]
    apply Iff.intro
    · intro_cases
      subst_vars
      tauto
    · intro_cases
      subst_vars
      tauto

theorem ConvergeWithPostCond.blockDone_iff:
    ConvergeWithPostCond Γ st sc (.expr (.block [] r)) Q ↔
    ConvergeWithPostCond Γ st sc (.expr r) (fun st' _ v => Q st' sc v) := by
  simp [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto


theorem ConvergeWithPostCond.declareVar_iff:
    ConvergeWithPostCond Γ st sc (.expr (.declareVar x v)) Q ↔
    ConvergeWithPostCond Γ st sc (.expr v) (fun st' sc' v' => sc' = sc ∧ Q st' (sc.update x (.value v')) ⟨.unit, ()⟩) := by
  simp [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto

theorem ConvergeWithPostCond.fresh_iff:
    ConvergeWithPostCond Γ st sc (.expr .fresh) Q ↔
    ∃v, Q st sc v := by
  simp [ConvergeWithPostCond]
  apply Iff.intro <;> {
    intro_cases
    subst_vars
    tauto
  }

theorem ConvergeWithPostCond.call_iff:
    ConvergeWithPostCond Γ st sc (.expr (.call f args)) Q ↔
    ConvergeWithPostCond Γ st sc (.callArgPrep f [] args) Q := by
  simp [ConvergeWithPostCond]

theorem ConvergeWithPostCond.callArgPrepNext_iff:
    ConvergeWithPostCond Γ st sc (.callArgPrep f as (e :: es)) Q ↔
    ConvergeWithPostCond Γ st sc (.expr e) (fun st' sc' v => sc' = sc ∧ ConvergeWithPostCond Γ st' sc (.callArgPrep f (as ++ [v]) es) Q) := by
  simp [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto

theorem ConvergeWithPostCond.var_value_iff (hp : sc x = some (.value v)):
    ConvergeWithPostCond Γ st sc (.expr (.var x)) Q ↔
    Q st sc v := by
  simp [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    subst_vars
    rename _ ∨ _ => hp
    simp_all
  · intro_cases
    subst_vars
    tauto

def BuiltinCWPC (b : Builtin) (as : List (Value P)) (Q : Value P → Prop): Prop :=
  ∃r, BigStepBuiltin P b as r ∧ Q r

theorem ConvergeWithPostCond.callArgsPrepDoneBuiltin_iff:
    ConvergeWithPostCond Γ st sc (.callArgPrep (.builtin b) as []) Q ↔
    BuiltinCWPC b as (fun r => Q st sc r) := by
  simp [ConvergeWithPostCond, BuiltinCWPC]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto

def CallWithPostCond (Γ : Env) (st : State P) (f : Function) (args : List (Value P)) (Q : State P → Value P → Prop): Prop :=
  ConvergeWithPostCond Γ st ((fun x => some (.value $ args.get! (f.params.indexOf x)))) (.expr f.body) (fun st' _ v => Q st' v)

theorem ConvergeWithPostCond.callArgPrepDeclDone_iff (hp : Γ fName = some f):
    ConvergeWithPostCond Γ st sc (.callArgPrep (.decl fName) args []) Q ↔
    CallWithPostCond Γ st f args (fun st v => Q st sc v) := by
  unfold CallWithPostCond
  unfold ConvergeWithPostCond
  conv in BigStepAux _ _ _ _ _ _ _ _ => rw [BigStepAux.callArgPrepDeclDone_iff _ hp]
  simp [BigStepCall]
  apply Iff.intro
  · intro_cases
    subst_vars
    repeat apply Exists.intro
    apply And.intro
    assumption
    assumption
  · intro_cases
    repeat apply Exists.intro
    apply And.intro
    apply And.intro
    apply Exists.intro
    assumption
    rfl
    assumption

theorem BuiltinCWPC.eq_iff :
  BuiltinCWPC .eq [a, b] Q ↔ Q ⟨.bool, a = b⟩ := by simp [BuiltinCWPC]; rfl

theorem BuiltinCWPC.assert_iff :
  BuiltinCWPC .assert [⟨.bool, p⟩] Q ↔ p ∧ Q ⟨.unit, ()⟩ := by
  simp [BuiltinCWPC]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto

theorem BuiltinCWPC.sub_u_iff :
  BuiltinCWPC .sub [⟨.u n, a⟩, ⟨.u n, b⟩] Q ↔ b.val ≤ a.val ∧ Q ⟨.u n, a - b⟩ := by
  simp [BuiltinCWPC, and_assoc]

theorem BuiltinCWPC.add_u_iff :
  BuiltinCWPC .add [⟨.u n, a⟩, ⟨.u n, b⟩] Q ↔ a.val + b.val < 2 ^ n ∧ Q ⟨.u n, a + b⟩ := by
  simp [BuiltinCWPC, and_assoc]

def IteWPC (Γ : Env) (st : State P) (sc : Scope P) (b : Value P) (t e : Expr) (Q : State P → Scope P → Value P → Prop): Prop :=
    (b = ⟨.bool, true⟩ ∧ ConvergeWithPostCond Γ st sc (.expr t) fun st sc' v => sc = sc' ∧ Q st sc v) ∨
    (b = ⟨.bool, false⟩ ∧ ConvergeWithPostCond Γ st sc (.expr e) fun st sc' v => sc = sc' ∧ Q st sc v)

theorem ConvergeWithPostCond.ite_iff:
    ConvergeWithPostCond Γ st sc (.expr (.ite b t e)) Q ↔
    ConvergeWithPostCond Γ st sc (.expr b) (fun st' sc' v => sc' = sc ∧ IteWPC Γ st' sc' v t e Q) := by
  simp [ConvergeWithPostCond, IteWPC]
  apply Iff.intro
  · intro_cases
    casesm* _ ∨ _, _ ∧ _
    all_goals (
      subst_vars
      repeat apply Exists.intro
      apply And.intro
      assumption
      simp
      repeat apply Exists.intro
      tauto
    )
  · intro_cases
    casesm* _ ∨ _
    · casesm* _ ∧ _, ∃_, _
      subst_vars
      repeat apply Exists.intro
      apply And.intro
      apply And.intro
      rfl
      repeat apply Exists.intro
      apply And.intro
      assumption
      apply Or.inl
      apply And.intro
      rfl
      assumption
      assumption
    · casesm* _ ∧ _, ∃_, _
      subst_vars
      repeat apply Exists.intro
      apply And.intro
      apply And.intro
      rfl
      repeat apply Exists.intro
      apply And.intro
      assumption
      apply Or.inr
      apply And.intro
      rfl
      assumption
      assumption

theorem IteWPC.iff_true (hb : b = true):
    IteWPC Γ st sc ⟨.bool, b⟩ t e Q ↔ ConvergeWithPostCond Γ st sc (.expr t) fun st sc' v => sc = sc' ∧ Q st sc v := by
  simp [IteWPC, hb]

theorem IteWPC.iff_false (hb : b = false):
    IteWPC Γ st sc ⟨.bool, b⟩ t e Q ↔ ConvergeWithPostCond Γ st sc (.expr e) fun st sc' v => sc = sc' ∧ Q st sc v := by
  simp [IteWPC, hb]

theorem ConvergeWithPostCond.lit_field_iff : ConvergeWithPostCond (P:=P) Γ st sc (.expr (.lit v .none)) Q ↔ Q st sc ⟨.field, (v : ZMod P)⟩ := by
  simp [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto

theorem ConvergeWithPostCond.lit_u_iff : ConvergeWithPostCond (P:=P) Γ st sc (.expr (.lit v (.some (.u n)))) Q ↔ Q st sc ⟨.u n, (v : U n)⟩ := by
  simp [ConvergeWithPostCond]
  apply Iff.intro
  · intro_cases
    subst_vars
    tauto
  · intro_cases
    subst_vars
    tauto


theorem BigStepAux.exists_fresh_iff' {Q : State P → Scope P → Value P → Prop}:
    (∃st' sc' v, BigStepAux P Γ st sc (.expr .fresh) st' sc' v ∧ Q st' sc' v) ↔
    ∃v, Q st sc v := by
  apply Iff.intro <;> { simp; intro_cases; tauto }

-- theorem BigStepAux

syntax "nr_simp_wip" : tactic
macro_rules
|`(tactic|nr_simp_wip) => `(tactic|
  simp (disch := (first | noir_simp_discharge | decide)) only [
    true_and,
    and_true,
    ConvergeWithPostCond.of_BigStepAux,
    ConvergeWithPostCond.blockNext_iff,
    ConvergeWithPostCond.declareVar_iff,
    ConvergeWithPostCond.fresh_iff,
    ConvergeWithPostCond.call_iff,
    ConvergeWithPostCond.callArgPrepNext_iff,
    ConvergeWithPostCond.var_value_iff,
    ConvergeWithPostCond.callArgsPrepDoneBuiltin_iff,
    ConvergeWithPostCond.blockDone_iff,
    List.nil_append,
    List.cons_append,
    List.indexOf_cons_ne,
    List.indexOf_cons_eq,
    List.get!_cons_succ,
    List.get!_cons_zero,
    decide_eq_true_iff,
    BuiltinCWPC.eq_iff,
    BuiltinCWPC.assert_iff,
    BuiltinCWPC.add_u_iff,
    BuiltinCWPC.sub_u_iff,
    ConvergeWithPostCond.ite_iff,
    IteWPC.iff_true,
    IteWPC.iff_false,
    ConvergeWithPostCond.lit_field_iff,
    ConvergeWithPostCond.lit_u_iff,

  ]
)

theorem assignableEq:
  ConvergeWithPostCond (Lampe.Env.ofModule testMod) st sc (.callArgPrep (.decl "assertEq") [a, b] []) Q ↔
  a = b ∧ Q st sc ⟨.unit, ()⟩ := by
  simp (disch := noir_simp_discharge) only [
    ConvergeWithPostCond.callArgPrepDeclDone_iff,
  ]
  unfold CallWithPostCond
  nr_simp_wip
  simp

theorem assignableRecursiveMul [Fact (Nat.Prime P)]:
    ConvergeWithPostCond (P := P) (Lampe.Env.ofModule testMod) st sc (.callArgPrep (.decl "recursiveMul") [⟨.u 64, a⟩, ⟨.u 64, b⟩] []) Q ↔
    (a.val * b.val < 2 ^ 64) ∧ Q st sc ⟨.u 64, a * b⟩ := by
  rcases a with ⟨a, ha⟩
  induction a generalizing sc Q with
  | zero =>
      simp (disch := noir_simp_discharge) only [
        ConvergeWithPostCond.callArgPrepDeclDone_iff,
      ]
      simp only [CallWithPostCond]
      nr_simp_wip
      simp
  | succ a ih =>
      simp (disch := noir_simp_discharge) only [
        ConvergeWithPostCond.callArgPrepDeclDone_iff,
      ]
      simp only [CallWithPostCond]
      have : decide (Value.mk (P := P) (.u 64) ⟨a + 1, ha⟩ = ⟨.u 64, 0⟩) = false := by
        simp
        rintro ⟨rfl⟩
      nr_simp_wip
      have : (Fin.mk (a + 1) ha) - ↑1 = Fin.mk a (by linarith) := by
        conv_lhs => whnf
        conv_rhs => whnf
        simp_arith
        linarith
      have : a < 2 ^ 64 := by linarith
      simp only [Nat.cast_one, *]
      nr_simp_wip




  -- noir_simp only
  -- crush
  -- induction a generalizing sc sc' v with
  -- | zero =>
  --   unfold BigStepCall
  --   crush
  --   tauto
  -- | succ a ih =>
  --   have ap1_def : (⟨a + 1, ha⟩ : ZMod (p+1)) = (⟨a, by linarith⟩) + 1 := by
  --     congr
  --     repeat (rw [Nat.mod_eq_of_lt] <;> try linarith)

  --   have : (⟨a, by linarith⟩: ZMod (p+1)) + 1 ≠ 0 := by
  --     intro h
  --     injection h with h
  --     repeat rw [Nat.mod_eq_of_lt] at h
  --     any_goals linarith
  --     rw [Nat.mod_eq_of_lt]
  --     any_goals linarith

  --   noir_simp only [this, ap1_def, ih]
  --   unfold BigStepCall
  --   crush
  --   simp only [this, ap1_def, ih]
  --   crush
  --   simp only [this, ap1_def, ih]
  --   crush
  --   ring_nf
  --   tauto

  -- crush
  -- tauto

example :
    ∃st' sc', BigStepAux 17 (stdlib.extend (Lampe.Env.ofModule testMod)) st sc (.callArgPrep (.decl "lt_fallback") [⟨.field, 10⟩, ⟨.field, 5⟩] []) st' sc' ⟨.bool, true⟩ := by
  simp (disch := with_unfolding_all rfl) only [BigStepAux.callArgPrepDeclDone_iff3]
  unfold BigStepCall
  crush
  simp [Field.numBits, Nat.log2]
  conv in (occs := *) (Fin.val _ / Fin.val _) => whnf
  simp [BigStepAux.loopCont_iff]
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
